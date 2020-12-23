%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7fHKVZR71i

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:35 EST 2020

% Result     : Theorem 11.99s
% Output     : Refutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 371 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          : 1168 (6069 expanded)
%              Number of equality atoms :    8 (  21 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t26_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( ( r1_orders_2 @ A @ B @ C )
                      & ( r1_orders_2 @ A @ C @ D ) )
                   => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r1_orders_2 @ A @ B @ C )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_orders_2])).

thf('0',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v4_orders_2 @ A )
      <=> ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ~ ( v4_orders_2 @ X18 )
      | ( r8_relat_2 @ ( u1_orders_2 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_2])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d8_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r8_relat_2 @ A @ B )
        <=> ! [C: $i,D: $i,E: $i] :
              ( ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ D @ B )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
                & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) )
             => ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r8_relat_2 @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X13 )
      | ~ ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ sk_B @ X1 )
      | ~ ( r2_hidden @ sk_C_1 @ X1 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_C_1 @ X1 ) @ ( u1_orders_2 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ X1 ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_C_1 @ X0 )
      | ~ ( r8_relat_2 @ ( u1_orders_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_E @ X8 @ X9 @ X10 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r2_hidden @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_F @ X8 @ X9 @ X10 ) @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r2_hidden @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k4_tarski @ ( sk_E @ X8 @ X9 @ X10 ) @ ( sk_F @ X8 @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( X1
        = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k4_tarski @ sk_B @ sk_C_1 )
    = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('58',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('61',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_hidden @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r2_hidden @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) ) @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( X1
        = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('77',plain,
    ( ( ( k4_tarski @ sk_C_1 @ sk_D_1 )
      = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k4_tarski @ sk_C_1 @ sk_D_1 )
    = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) @ ( sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ ( k4_tarski @ sk_C_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('82',plain,(
    r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r2_hidden @ ( k4_tarski @ sk_B @ sk_D_1 ) @ ( u1_orders_2 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','58','61','82'])).

thf('84',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('85',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_D_1 ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['0','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7fHKVZR71i
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:13:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 11.99/12.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.99/12.21  % Solved by: fo/fo7.sh
% 11.99/12.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.99/12.21  % done 2742 iterations in 11.763s
% 11.99/12.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.99/12.21  % SZS output start Refutation
% 11.99/12.21  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.99/12.21  thf(sk_D_1_type, type, sk_D_1: $i).
% 11.99/12.21  thf(sk_B_type, type, sk_B: $i).
% 11.99/12.21  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 11.99/12.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.99/12.21  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 11.99/12.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.99/12.21  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 11.99/12.21  thf(sk_A_type, type, sk_A: $i).
% 11.99/12.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.99/12.21  thf(r8_relat_2_type, type, r8_relat_2: $i > $i > $o).
% 11.99/12.21  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 11.99/12.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 11.99/12.21  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 11.99/12.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.99/12.21  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 11.99/12.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.99/12.21  thf(sk_C_1_type, type, sk_C_1: $i).
% 11.99/12.21  thf(t26_orders_2, conjecture,
% 11.99/12.21    (![A:$i]:
% 11.99/12.21     ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.99/12.21       ( ![B:$i]:
% 11.99/12.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21           ( ![C:$i]:
% 11.99/12.21             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21               ( ![D:$i]:
% 11.99/12.21                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21                   ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 11.99/12.21                       ( r1_orders_2 @ A @ C @ D ) ) =>
% 11.99/12.21                     ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 11.99/12.21  thf(zf_stmt_0, negated_conjecture,
% 11.99/12.21    (~( ![A:$i]:
% 11.99/12.21        ( ( ( v4_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 11.99/12.21          ( ![B:$i]:
% 11.99/12.21            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21              ( ![C:$i]:
% 11.99/12.21                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21                  ( ![D:$i]:
% 11.99/12.21                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21                      ( ( ( r1_orders_2 @ A @ B @ C ) & 
% 11.99/12.21                          ( r1_orders_2 @ A @ C @ D ) ) =>
% 11.99/12.21                        ( r1_orders_2 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 11.99/12.21    inference('cnf.neg', [status(esa)], [t26_orders_2])).
% 11.99/12.21  thf('0', plain, (~ (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf(d5_orders_2, axiom,
% 11.99/12.21    (![A:$i]:
% 11.99/12.21     ( ( l1_orders_2 @ A ) =>
% 11.99/12.21       ( ( v4_orders_2 @ A ) <=>
% 11.99/12.21         ( r8_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 11.99/12.21  thf('1', plain,
% 11.99/12.21      (![X18 : $i]:
% 11.99/12.21         (~ (v4_orders_2 @ X18)
% 11.99/12.21          | (r8_relat_2 @ (u1_orders_2 @ X18) @ (u1_struct_0 @ X18))
% 11.99/12.21          | ~ (l1_orders_2 @ X18))),
% 11.99/12.21      inference('cnf', [status(esa)], [d5_orders_2])).
% 11.99/12.21  thf('2', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf(d9_orders_2, axiom,
% 11.99/12.21    (![A:$i]:
% 11.99/12.21     ( ( l1_orders_2 @ A ) =>
% 11.99/12.21       ( ![B:$i]:
% 11.99/12.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21           ( ![C:$i]:
% 11.99/12.21             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 11.99/12.21               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 11.99/12.21                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 11.99/12.21  thf('4', plain,
% 11.99/12.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.99/12.21         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 11.99/12.21          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (l1_orders_2 @ X20))),
% 11.99/12.21      inference('cnf', [status(esa)], [d9_orders_2])).
% 11.99/12.21  thf('5', plain,
% 11.99/12.21      (![X0 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ sk_A)
% 11.99/12.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 11.99/12.21      inference('sup-', [status(thm)], ['3', '4'])).
% 11.99/12.21  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('7', plain,
% 11.99/12.21      (![X0 : $i]:
% 11.99/12.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r1_orders_2 @ sk_A @ sk_C_1 @ X0))),
% 11.99/12.21      inference('demod', [status(thm)], ['5', '6'])).
% 11.99/12.21  thf('8', plain,
% 11.99/12.21      ((~ (r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)
% 11.99/12.21        | (r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['2', '7'])).
% 11.99/12.21  thf('9', plain, ((r1_orders_2 @ sk_A @ sk_C_1 @ sk_D_1)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('10', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['8', '9'])).
% 11.99/12.21  thf(dt_u1_orders_2, axiom,
% 11.99/12.21    (![A:$i]:
% 11.99/12.21     ( ( l1_orders_2 @ A ) =>
% 11.99/12.21       ( m1_subset_1 @
% 11.99/12.21         ( u1_orders_2 @ A ) @ 
% 11.99/12.21         ( k1_zfmisc_1 @
% 11.99/12.21           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 11.99/12.21  thf('11', plain,
% 11.99/12.21      (![X22 : $i]:
% 11.99/12.21         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 11.99/12.21           (k1_zfmisc_1 @ 
% 11.99/12.21            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 11.99/12.21          | ~ (l1_orders_2 @ X22))),
% 11.99/12.21      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 11.99/12.21  thf(cc1_relset_1, axiom,
% 11.99/12.21    (![A:$i,B:$i,C:$i]:
% 11.99/12.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.99/12.21       ( v1_relat_1 @ C ) ))).
% 11.99/12.21  thf('12', plain,
% 11.99/12.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 11.99/12.21         ((v1_relat_1 @ X5)
% 11.99/12.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 11.99/12.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 11.99/12.21  thf('13', plain,
% 11.99/12.21      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['11', '12'])).
% 11.99/12.21  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('16', plain,
% 11.99/12.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.99/12.21         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (r1_orders_2 @ X20 @ X19 @ X21)
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 11.99/12.21          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (l1_orders_2 @ X20))),
% 11.99/12.21      inference('cnf', [status(esa)], [d9_orders_2])).
% 11.99/12.21  thf('17', plain,
% 11.99/12.21      (![X0 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ sk_A)
% 11.99/12.21          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 11.99/12.21      inference('sup-', [status(thm)], ['15', '16'])).
% 11.99/12.21  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('19', plain,
% 11.99/12.21      (![X0 : $i]:
% 11.99/12.21         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r1_orders_2 @ sk_A @ sk_B @ X0))),
% 11.99/12.21      inference('demod', [status(thm)], ['17', '18'])).
% 11.99/12.21  thf('20', plain,
% 11.99/12.21      ((~ (r1_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 11.99/12.21        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['14', '19'])).
% 11.99/12.21  thf('21', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('22', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['20', '21'])).
% 11.99/12.21  thf(d8_relat_2, axiom,
% 11.99/12.21    (![A:$i]:
% 11.99/12.21     ( ( v1_relat_1 @ A ) =>
% 11.99/12.21       ( ![B:$i]:
% 11.99/12.21         ( ( r8_relat_2 @ A @ B ) <=>
% 11.99/12.21           ( ![C:$i,D:$i,E:$i]:
% 11.99/12.21             ( ( ( r2_hidden @ C @ B ) & ( r2_hidden @ D @ B ) & 
% 11.99/12.21                 ( r2_hidden @ E @ B ) & 
% 11.99/12.21                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) & 
% 11.99/12.21                 ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) =>
% 11.99/12.21               ( r2_hidden @ ( k4_tarski @ C @ E ) @ A ) ) ) ) ) ))).
% 11.99/12.21  thf('23', plain,
% 11.99/12.21      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 11.99/12.21         (~ (r8_relat_2 @ X13 @ X14)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X13)
% 11.99/12.21          | ~ (r2_hidden @ X16 @ X14)
% 11.99/12.21          | ~ (r2_hidden @ X15 @ X14)
% 11.99/12.21          | ~ (r2_hidden @ X17 @ X14)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X13)
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ X15 @ X17) @ X13)
% 11.99/12.21          | ~ (v1_relat_1 @ X13))),
% 11.99/12.21      inference('cnf', [status(esa)], [d8_relat_2])).
% 11.99/12.21  thf('24', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_B @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X0) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r2_hidden @ X0 @ X1)
% 11.99/12.21          | ~ (r2_hidden @ sk_B @ X1)
% 11.99/12.21          | ~ (r2_hidden @ sk_C_1 @ X1)
% 11.99/12.21          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X1))),
% 11.99/12.21      inference('sup-', [status(thm)], ['22', '23'])).
% 11.99/12.21  thf('25', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ sk_A)
% 11.99/12.21          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_C_1 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_B @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['13', '24'])).
% 11.99/12.21  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('27', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_C_1 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_B @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ sk_C_1 @ X1) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | (r2_hidden @ (k4_tarski @ sk_B @ X1) @ (u1_orders_2 @ sk_A)))),
% 11.99/12.21      inference('demod', [status(thm)], ['25', '26'])).
% 11.99/12.21  thf('28', plain,
% 11.99/12.21      (![X0 : $i]:
% 11.99/12.21         ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))
% 11.99/12.21          | ~ (r2_hidden @ sk_D_1 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_B @ X0)
% 11.99/12.21          | ~ (r2_hidden @ sk_C_1 @ X0)
% 11.99/12.21          | ~ (r8_relat_2 @ (u1_orders_2 @ sk_A) @ X0))),
% 11.99/12.21      inference('sup-', [status(thm)], ['10', '27'])).
% 11.99/12.21  thf('29', plain,
% 11.99/12.21      ((~ (l1_orders_2 @ sk_A)
% 11.99/12.21        | ~ (v4_orders_2 @ sk_A)
% 11.99/12.21        | ~ (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 11.99/12.21        | (r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['1', '28'])).
% 11.99/12.21  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('31', plain, ((v4_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('32', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['20', '21'])).
% 11.99/12.21  thf('33', plain,
% 11.99/12.21      (![X22 : $i]:
% 11.99/12.21         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 11.99/12.21           (k1_zfmisc_1 @ 
% 11.99/12.21            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 11.99/12.21          | ~ (l1_orders_2 @ X22))),
% 11.99/12.21      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 11.99/12.21  thf(t6_relset_1, axiom,
% 11.99/12.21    (![A:$i,B:$i,C:$i,D:$i]:
% 11.99/12.21     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 11.99/12.21       ( ~( ( r2_hidden @ A @ D ) & 
% 11.99/12.21            ( ![E:$i,F:$i]:
% 11.99/12.21              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 11.99/12.21                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 11.99/12.21  thf('34', plain,
% 11.99/12.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 11.99/12.21         ((r2_hidden @ (sk_E @ X8 @ X9 @ X10) @ X9)
% 11.99/12.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 11.99/12.21          | ~ (r2_hidden @ X10 @ X11))),
% 11.99/12.21      inference('cnf', [status(esa)], [t6_relset_1])).
% 11.99/12.21  thf('35', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21             (u1_struct_0 @ X0)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['33', '34'])).
% 11.99/12.21  thf('36', plain,
% 11.99/12.21      (((r2_hidden @ 
% 11.99/12.21         (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21         (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['32', '35'])).
% 11.99/12.21  thf('37', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('38', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21         (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21        (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['36', '37'])).
% 11.99/12.21  thf('39', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['20', '21'])).
% 11.99/12.21  thf('40', plain,
% 11.99/12.21      (![X22 : $i]:
% 11.99/12.21         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 11.99/12.21           (k1_zfmisc_1 @ 
% 11.99/12.21            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 11.99/12.21          | ~ (l1_orders_2 @ X22))),
% 11.99/12.21      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 11.99/12.21  thf('41', plain,
% 11.99/12.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 11.99/12.21         ((r2_hidden @ (sk_F @ X8 @ X9 @ X10) @ X8)
% 11.99/12.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 11.99/12.21          | ~ (r2_hidden @ X10 @ X11))),
% 11.99/12.21      inference('cnf', [status(esa)], [t6_relset_1])).
% 11.99/12.21  thf('42', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21             (u1_struct_0 @ X0)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['40', '41'])).
% 11.99/12.21  thf('43', plain,
% 11.99/12.21      (((r2_hidden @ 
% 11.99/12.21         (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21         (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['39', '42'])).
% 11.99/12.21  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('45', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21         (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21        (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['43', '44'])).
% 11.99/12.21  thf(l54_zfmisc_1, axiom,
% 11.99/12.21    (![A:$i,B:$i,C:$i,D:$i]:
% 11.99/12.21     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 11.99/12.21       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 11.99/12.21  thf('46', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 11.99/12.21         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 11.99/12.21          | ~ (r2_hidden @ X2 @ X4)
% 11.99/12.21          | ~ (r2_hidden @ X0 @ X1))),
% 11.99/12.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 11.99/12.21  thf('47', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (r2_hidden @ X1 @ X0)
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (k4_tarski @ X1 @ 
% 11.99/12.21              (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21               (k4_tarski @ sk_B @ sk_C_1))) @ 
% 11.99/12.21             (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))),
% 11.99/12.21      inference('sup-', [status(thm)], ['45', '46'])).
% 11.99/12.21  thf('48', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (k4_tarski @ 
% 11.99/12.21         (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21         (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_B @ sk_C_1))) @ 
% 11.99/12.21        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['38', '47'])).
% 11.99/12.21  thf('49', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['20', '21'])).
% 11.99/12.21  thf('50', plain,
% 11.99/12.21      (![X22 : $i]:
% 11.99/12.21         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 11.99/12.21           (k1_zfmisc_1 @ 
% 11.99/12.21            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 11.99/12.21          | ~ (l1_orders_2 @ X22))),
% 11.99/12.21      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 11.99/12.21  thf('51', plain,
% 11.99/12.21      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 11.99/12.21         (((X10)
% 11.99/12.21            = (k4_tarski @ (sk_E @ X8 @ X9 @ X10) @ (sk_F @ X8 @ X9 @ X10)))
% 11.99/12.21          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 11.99/12.21          | ~ (r2_hidden @ X10 @ X11))),
% 11.99/12.21      inference('cnf', [status(esa)], [t6_relset_1])).
% 11.99/12.21  thf('52', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | ((X1)
% 11.99/12.21              = (k4_tarski @ 
% 11.99/12.21                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1))))),
% 11.99/12.21      inference('sup-', [status(thm)], ['50', '51'])).
% 11.99/12.21  thf('53', plain,
% 11.99/12.21      ((((k4_tarski @ sk_B @ sk_C_1)
% 11.99/12.21          = (k4_tarski @ 
% 11.99/12.21             (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21              (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21             (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21              (k4_tarski @ sk_B @ sk_C_1))))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['49', '52'])).
% 11.99/12.21  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('55', plain,
% 11.99/12.21      (((k4_tarski @ sk_B @ sk_C_1)
% 11.99/12.21         = (k4_tarski @ 
% 11.99/12.21            (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21             (k4_tarski @ sk_B @ sk_C_1)) @ 
% 11.99/12.21            (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21             (k4_tarski @ sk_B @ sk_C_1))))),
% 11.99/12.21      inference('demod', [status(thm)], ['53', '54'])).
% 11.99/12.21  thf('56', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 11.99/12.21        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('demod', [status(thm)], ['48', '55'])).
% 11.99/12.21  thf('57', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.99/12.21         ((r2_hidden @ X2 @ X3)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 11.99/12.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 11.99/12.21  thf('58', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['56', '57'])).
% 11.99/12.21  thf('59', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ 
% 11.99/12.21        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('demod', [status(thm)], ['48', '55'])).
% 11.99/12.21  thf('60', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.99/12.21         ((r2_hidden @ X0 @ X1)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 11.99/12.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 11.99/12.21  thf('61', plain, ((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['59', '60'])).
% 11.99/12.21  thf('62', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['8', '9'])).
% 11.99/12.21  thf('63', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21             (u1_struct_0 @ X0)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['33', '34'])).
% 11.99/12.21  thf('64', plain,
% 11.99/12.21      (((r2_hidden @ 
% 11.99/12.21         (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21         (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['62', '63'])).
% 11.99/12.21  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('66', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21         (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21        (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['64', '65'])).
% 11.99/12.21  thf('67', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['8', '9'])).
% 11.99/12.21  thf('68', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21             (u1_struct_0 @ X0)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['40', '41'])).
% 11.99/12.21  thf('69', plain,
% 11.99/12.21      (((r2_hidden @ 
% 11.99/12.21         (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21         (u1_struct_0 @ sk_A))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['67', '68'])).
% 11.99/12.21  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('71', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21         (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21        (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['69', '70'])).
% 11.99/12.21  thf('72', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 11.99/12.21         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 11.99/12.21          | ~ (r2_hidden @ X2 @ X4)
% 11.99/12.21          | ~ (r2_hidden @ X0 @ X1))),
% 11.99/12.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 11.99/12.21  thf('73', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (r2_hidden @ X1 @ X0)
% 11.99/12.21          | (r2_hidden @ 
% 11.99/12.21             (k4_tarski @ X1 @ 
% 11.99/12.21              (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21               (k4_tarski @ sk_C_1 @ sk_D_1))) @ 
% 11.99/12.21             (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))),
% 11.99/12.21      inference('sup-', [status(thm)], ['71', '72'])).
% 11.99/12.21  thf('74', plain,
% 11.99/12.21      ((r2_hidden @ 
% 11.99/12.21        (k4_tarski @ 
% 11.99/12.21         (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21         (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21          (k4_tarski @ sk_C_1 @ sk_D_1))) @ 
% 11.99/12.21        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['66', '73'])).
% 11.99/12.21  thf('75', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['8', '9'])).
% 11.99/12.21  thf('76', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i]:
% 11.99/12.21         (~ (l1_orders_2 @ X0)
% 11.99/12.21          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 11.99/12.21          | ((X1)
% 11.99/12.21              = (k4_tarski @ 
% 11.99/12.21                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 11.99/12.21                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1))))),
% 11.99/12.21      inference('sup-', [status(thm)], ['50', '51'])).
% 11.99/12.21  thf('77', plain,
% 11.99/12.21      ((((k4_tarski @ sk_C_1 @ sk_D_1)
% 11.99/12.21          = (k4_tarski @ 
% 11.99/12.21             (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21              (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21             (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21              (k4_tarski @ sk_C_1 @ sk_D_1))))
% 11.99/12.21        | ~ (l1_orders_2 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['75', '76'])).
% 11.99/12.21  thf('78', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('79', plain,
% 11.99/12.21      (((k4_tarski @ sk_C_1 @ sk_D_1)
% 11.99/12.21         = (k4_tarski @ 
% 11.99/12.21            (sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21             (k4_tarski @ sk_C_1 @ sk_D_1)) @ 
% 11.99/12.21            (sk_F @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 11.99/12.21             (k4_tarski @ sk_C_1 @ sk_D_1))))),
% 11.99/12.21      inference('demod', [status(thm)], ['77', '78'])).
% 11.99/12.21  thf('80', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_C_1 @ sk_D_1) @ 
% 11.99/12.21        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('demod', [status(thm)], ['74', '79'])).
% 11.99/12.21  thf('81', plain,
% 11.99/12.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.99/12.21         ((r2_hidden @ X2 @ X3)
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 11.99/12.21      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 11.99/12.21  thf('82', plain, ((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('sup-', [status(thm)], ['80', '81'])).
% 11.99/12.21  thf('83', plain,
% 11.99/12.21      ((r2_hidden @ (k4_tarski @ sk_B @ sk_D_1) @ (u1_orders_2 @ sk_A))),
% 11.99/12.21      inference('demod', [status(thm)], ['29', '30', '31', '58', '61', '82'])).
% 11.99/12.21  thf('84', plain,
% 11.99/12.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 11.99/12.21         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 11.99/12.21          | (r1_orders_2 @ X20 @ X19 @ X21)
% 11.99/12.21          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 11.99/12.21          | ~ (l1_orders_2 @ X20))),
% 11.99/12.21      inference('cnf', [status(esa)], [d9_orders_2])).
% 11.99/12.21  thf('85', plain,
% 11.99/12.21      ((~ (l1_orders_2 @ sk_A)
% 11.99/12.21        | ~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))
% 11.99/12.21        | (r1_orders_2 @ sk_A @ sk_B @ sk_D_1)
% 11.99/12.21        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 11.99/12.21      inference('sup-', [status(thm)], ['83', '84'])).
% 11.99/12.21  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('87', plain, ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('88', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 11.99/12.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.99/12.21  thf('89', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_D_1)),
% 11.99/12.21      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 11.99/12.21  thf('90', plain, ($false), inference('demod', [status(thm)], ['0', '89'])).
% 11.99/12.21  
% 11.99/12.21  % SZS output end Refutation
% 11.99/12.21  
% 11.99/12.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
