%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9yPBgLvT3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 410 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   26
%              Number of atoms          : 1119 (5171 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t76_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
     => ! [E: $i] :
          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
         => ! [F: $i] :
              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                 => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                   => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                      & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                      & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
       => ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                   => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                     => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                        & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                        & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_mcart_1])).

thf('9',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('15',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['26','29'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('51',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('58',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['51','60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('63',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('67',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['19'])).

thf('72',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('74',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('75',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('80',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('82',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('84',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('86',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('90',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('94',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('96',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['67','94','95'])).

thf('97',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['20','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','97'])).

thf('99',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['56','57'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('104',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','39'])).

thf('114',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['15','112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['12','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m9yPBgLvT3
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 175 iterations in 0.072s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.52  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf(t10_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.21/0.52          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(d3_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.52  thf(t76_mcart_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ![E:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.52           ( ![F:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.52               ( ![G:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.52                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.52                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.52                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52          ( ![E:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.52              ( ![F:$i]:
% 0.21/0.52                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.52                  ( ![G:$i]:
% 0.21/0.52                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.52                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.52                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.52                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.21/0.52  thf('9', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('11', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.52  thf('13', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_subset_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.52          | (v1_xboole_0 @ X9)
% 0.21/0.52          | ~ (v1_xboole_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('15', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t50_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ~( ![D:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.52                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.52                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.52                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.52                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.52         (((X21) = (k1_xboole_0))
% 0.21/0.52          | ((X22) = (k1_xboole_0))
% 0.21/0.52          | ((k6_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.21/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.21/0.52          | ((X24) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.21/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.21/0.52        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.21/0.52        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.52         (((X21) = (k1_xboole_0))
% 0.21/0.52          | ((X22) = (k1_xboole_0))
% 0.21/0.52          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.21/0.52          | ((X24) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.21/0.52          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0))
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '30'])).
% 0.21/0.52  thf('32', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.52          | (v1_xboole_0 @ X9)
% 0.21/0.52          | ~ (v1_xboole_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('34', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_F)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '34'])).
% 0.21/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.52  thf('36', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf(t7_ordinal1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (((((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_F)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.52  thf('42', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('44', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('clc', [status(thm)], ['41', '44'])).
% 0.21/0.52  thf('46', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.52          | (v1_xboole_0 @ X9)
% 0.21/0.52          | ~ (v1_xboole_0 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.52  thf('48', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_E)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.52  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.21/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.21/0.52          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.52          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.21/0.52          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('58', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('60', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('clc', [status(thm)], ['51', '60'])).
% 0.21/0.52  thf('62', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.52  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_D))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.52         (((X21) = (k1_xboole_0))
% 0.21/0.52          | ((X22) = (k1_xboole_0))
% 0.21/0.52          | ((k5_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.21/0.52              = (k1_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.21/0.52          | ((X24) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.21/0.52            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '55'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.21/0.52          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('75', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0))
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '75'])).
% 0.21/0.52  thf('77', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_F)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (((((sk_B_1) = (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_F)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('clc', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52         | ((sk_A) = (k1_xboole_0))
% 0.21/0.52         | (v1_xboole_0 @ sk_E)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.52  thf('87', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.52  thf('89', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.52  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (((v1_xboole_0 @ sk_D))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.52  thf('93', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.21/0.52       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)) | 
% 0.21/0.52       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['67', '94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['20', '96'])).
% 0.21/0.52  thf('98', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '97'])).
% 0.21/0.52  thf('99', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.52  thf('101', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('102', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | (v1_xboole_0 @ sk_F))),
% 0.21/0.52      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.52  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('104', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | (v1_xboole_0 @ sk_F))),
% 0.21/0.52      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.52  thf('105', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('106', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['104', '105'])).
% 0.21/0.52  thf('107', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | (v1_xboole_0 @ sk_E))),
% 0.21/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.52  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('110', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.21/0.52      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.52  thf('111', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['110', '111'])).
% 0.21/0.52  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf('114', plain, ((v1_xboole_0 @ sk_D)),
% 0.21/0.52      inference('demod', [status(thm)], ['15', '112', '113'])).
% 0.21/0.52  thf('115', plain, ($false), inference('demod', [status(thm)], ['12', '114'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
