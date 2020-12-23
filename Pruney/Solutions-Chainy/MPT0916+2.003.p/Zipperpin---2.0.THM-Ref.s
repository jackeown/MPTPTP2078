%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K5r4urTs2E

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 410 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   26
%              Number of atoms          : 1119 (5171 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('18',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('57',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('60',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('65',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('69',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['19'])).

thf('74',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['58','59'])).

thf('76',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('80',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('82',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('84',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('86',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('90',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('94',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['19'])).

thf('96',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['69','94','95'])).

thf('97',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['20','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','97'])).

thf('99',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['44','47'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('102',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('104',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('106',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf('114',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['15','112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['12','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K5r4urTs2E
% 0.11/0.31  % Computer   : n015.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:49:23 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.32  % Running in FO mode
% 0.17/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.46  % Solved by: fo/fo7.sh
% 0.17/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.46  % done 137 iterations in 0.047s
% 0.17/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.46  % SZS output start Refutation
% 0.17/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.17/0.46  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.17/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.17/0.46  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.17/0.46  thf(sk_F_type, type, sk_F: $i).
% 0.17/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.17/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.17/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.17/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.17/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.17/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.17/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.17/0.46  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.17/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.17/0.46  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.17/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.17/0.46  thf(sk_G_type, type, sk_G: $i).
% 0.17/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.46  thf(d1_xboole_0, axiom,
% 0.17/0.46    (![A:$i]:
% 0.17/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.17/0.46  thf('0', plain,
% 0.17/0.46      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.17/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.46  thf(t10_mcart_1, axiom,
% 0.17/0.46    (![A:$i,B:$i,C:$i]:
% 0.17/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.17/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.17/0.46         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.17/0.46  thf('1', plain,
% 0.17/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.46         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.17/0.46          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.17/0.46  thf('2', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]:
% 0.17/0.46         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.17/0.46          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.17/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.17/0.46  thf('3', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.17/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.46  thf('4', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]:
% 0.17/0.46         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.17/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.17/0.46  thf(d3_zfmisc_1, axiom,
% 0.17/0.46    (![A:$i,B:$i,C:$i]:
% 0.17/0.46     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.17/0.46       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.17/0.46  thf('5', plain,
% 0.17/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.46         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.17/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.17/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.17/0.46  thf('6', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]:
% 0.17/0.46         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.17/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.17/0.46  thf('7', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.46         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.17/0.46          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.17/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.17/0.46  thf('8', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.17/0.46         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.17/0.46  thf(t76_mcart_1, conjecture,
% 0.17/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.46     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.46       ( ![E:$i]:
% 0.17/0.46         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.17/0.46           ( ![F:$i]:
% 0.17/0.46             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.17/0.46               ( ![G:$i]:
% 0.17/0.46                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.17/0.46                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.17/0.46                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.17/0.46                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.17/0.46                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.17/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.17/0.46        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.17/0.46          ( ![E:$i]:
% 0.17/0.46            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.17/0.46              ( ![F:$i]:
% 0.17/0.46                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.17/0.46                  ( ![G:$i]:
% 0.17/0.46                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.17/0.46                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.17/0.46                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.17/0.46                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.17/0.46                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.17/0.46    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.17/0.46  thf('9', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('10', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.17/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.46  thf('11', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.17/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.17/0.46  thf('12', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.17/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.17/0.46  thf('13', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf(cc1_subset_1, axiom,
% 0.17/0.46    (![A:$i]:
% 0.17/0.46     ( ( v1_xboole_0 @ A ) =>
% 0.17/0.46       ( ![B:$i]:
% 0.17/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.17/0.46  thf('14', plain,
% 0.17/0.46      (![X4 : $i, X5 : $i]:
% 0.17/0.46         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.17/0.46          | (v1_xboole_0 @ X4)
% 0.17/0.46          | ~ (v1_xboole_0 @ X5))),
% 0.17/0.46      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.17/0.46  thf('15', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.17/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.46  thf('16', plain,
% 0.17/0.46      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf(t50_mcart_1, axiom,
% 0.17/0.46    (![A:$i,B:$i,C:$i]:
% 0.17/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.17/0.46          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.17/0.46          ( ~( ![D:$i]:
% 0.17/0.46               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.17/0.46                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.17/0.46                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.17/0.46                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.17/0.46                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.17/0.46                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.17/0.46  thf('17', plain,
% 0.17/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.17/0.46         (((X16) = (k1_xboole_0))
% 0.17/0.46          | ((X17) = (k1_xboole_0))
% 0.17/0.46          | ((k7_mcart_1 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.17/0.46          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.17/0.46          | ((X19) = (k1_xboole_0)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.17/0.46  thf('18', plain,
% 0.17/0.46      ((((sk_C) = (k1_xboole_0))
% 0.17/0.46        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.17/0.46        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.17/0.46  thf('19', plain,
% 0.17/0.46      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.17/0.46        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.17/0.46        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('20', plain,
% 0.17/0.46      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.17/0.46      inference('split', [status(esa)], ['19'])).
% 0.17/0.46  thf('21', plain,
% 0.17/0.46      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('22', plain,
% 0.17/0.46      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.17/0.46         (((X16) = (k1_xboole_0))
% 0.17/0.46          | ((X17) = (k1_xboole_0))
% 0.17/0.46          | ((k5_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.17/0.46              = (k1_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.17/0.46          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.17/0.46          | ((X19) = (k1_xboole_0)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.17/0.46  thf('23', plain,
% 0.17/0.46      ((((sk_C) = (k1_xboole_0))
% 0.17/0.46        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.17/0.46            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.17/0.46        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.17/0.46  thf('24', plain,
% 0.17/0.46      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('split', [status(esa)], ['19'])).
% 0.17/0.46  thf('25', plain,
% 0.17/0.46      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.17/0.46         | ((sk_A) = (k1_xboole_0))
% 0.17/0.46         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.46         | ((sk_C) = (k1_xboole_0))))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.17/0.46  thf('26', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('27', plain,
% 0.17/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.46         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.17/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.17/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.17/0.46  thf('28', plain,
% 0.17/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.46         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.17/0.46          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.17/0.46  thf('29', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.46         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.17/0.46          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.17/0.46  thf('30', plain,
% 0.17/0.46      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.17/0.46      inference('sup-', [status(thm)], ['26', '29'])).
% 0.17/0.46  thf('31', plain,
% 0.17/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.46         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.17/0.46          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.17/0.46  thf('32', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.17/0.46      inference('sup-', [status(thm)], ['30', '31'])).
% 0.17/0.46  thf('33', plain,
% 0.17/0.46      (((((sk_A) = (k1_xboole_0))
% 0.17/0.46         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.46         | ((sk_C) = (k1_xboole_0))))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('demod', [status(thm)], ['25', '32'])).
% 0.17/0.46  thf('34', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('35', plain,
% 0.17/0.46      (![X4 : $i, X5 : $i]:
% 0.17/0.46         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.17/0.46          | (v1_xboole_0 @ X4)
% 0.17/0.46          | ~ (v1_xboole_0 @ X5))),
% 0.17/0.46      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.17/0.46  thf('36', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.17/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.17/0.46  thf('37', plain,
% 0.17/0.46      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.46         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.46         | ((sk_A) = (k1_xboole_0))
% 0.17/0.46         | (v1_xboole_0 @ sk_F)))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['33', '36'])).
% 0.17/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.17/0.46  thf('38', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.17/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.17/0.46  thf('39', plain,
% 0.17/0.46      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.17/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.46  thf(t7_ordinal1, axiom,
% 0.17/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.17/0.46  thf('40', plain,
% 0.17/0.46      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.17/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.17/0.46  thf('41', plain,
% 0.17/0.46      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['39', '40'])).
% 0.17/0.46  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.46      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.46  thf('43', plain,
% 0.17/0.46      (((((sk_B_1) = (k1_xboole_0))
% 0.17/0.46         | ((sk_A) = (k1_xboole_0))
% 0.17/0.46         | (v1_xboole_0 @ sk_F)))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('demod', [status(thm)], ['37', '42'])).
% 0.17/0.46  thf('44', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('45', plain,
% 0.17/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.17/0.46         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.17/0.46           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.17/0.46      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.17/0.46  thf('46', plain,
% 0.17/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.46         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.17/0.46          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.17/0.46  thf('47', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.17/0.46         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.17/0.46          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.17/0.46      inference('sup-', [status(thm)], ['45', '46'])).
% 0.17/0.46  thf('48', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.17/0.46      inference('sup-', [status(thm)], ['44', '47'])).
% 0.17/0.46  thf('49', plain,
% 0.17/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.17/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.46  thf('50', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.17/0.46      inference('sup-', [status(thm)], ['48', '49'])).
% 0.17/0.46  thf('51', plain,
% 0.17/0.46      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('clc', [status(thm)], ['43', '50'])).
% 0.17/0.46  thf('52', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.17/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.46  thf('53', plain,
% 0.17/0.46      (![X4 : $i, X5 : $i]:
% 0.17/0.46         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.17/0.46          | (v1_xboole_0 @ X4)
% 0.17/0.46          | ~ (v1_xboole_0 @ X5))),
% 0.17/0.46      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.17/0.46  thf('54', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.17/0.46      inference('sup-', [status(thm)], ['52', '53'])).
% 0.17/0.46  thf('55', plain,
% 0.17/0.46      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.46         | ((sk_A) = (k1_xboole_0))
% 0.17/0.46         | (v1_xboole_0 @ sk_E)))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('sup-', [status(thm)], ['51', '54'])).
% 0.17/0.46  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.46      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.46  thf('57', plain,
% 0.17/0.46      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.17/0.46         <= (~
% 0.17/0.46             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.46      inference('demod', [status(thm)], ['55', '56'])).
% 0.17/0.46  thf('58', plain,
% 0.17/0.46      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.17/0.46      inference('sup-', [status(thm)], ['26', '29'])).
% 0.17/0.46  thf('59', plain,
% 0.17/0.46      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.17/0.46         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.17/0.46          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.17/0.46      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.17/0.46  thf('60', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.17/0.46      inference('sup-', [status(thm)], ['58', '59'])).
% 0.17/0.47  thf('61', plain,
% 0.17/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.17/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.17/0.47  thf('62', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.17/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.17/0.47  thf('63', plain,
% 0.17/0.47      ((((sk_A) = (k1_xboole_0)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.47      inference('clc', [status(thm)], ['57', '62'])).
% 0.17/0.47  thf('64', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.17/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.47  thf('65', plain,
% 0.17/0.47      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['63', '64'])).
% 0.17/0.47  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('67', plain,
% 0.17/0.47      (((v1_xboole_0 @ sk_D))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.17/0.47      inference('demod', [status(thm)], ['65', '66'])).
% 0.17/0.47  thf('68', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.17/0.47      inference('sup-', [status(thm)], ['8', '11'])).
% 0.17/0.47  thf('69', plain,
% 0.17/0.47      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.17/0.47      inference('sup-', [status(thm)], ['67', '68'])).
% 0.17/0.47  thf('70', plain,
% 0.17/0.47      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.17/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.47  thf('71', plain,
% 0.17/0.47      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.17/0.47         (((X16) = (k1_xboole_0))
% 0.17/0.47          | ((X17) = (k1_xboole_0))
% 0.17/0.47          | ((k6_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.17/0.47              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.17/0.47          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.17/0.47          | ((X19) = (k1_xboole_0)))),
% 0.17/0.47      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.17/0.47  thf('72', plain,
% 0.17/0.47      ((((sk_C) = (k1_xboole_0))
% 0.17/0.47        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.17/0.47            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.17/0.47        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['70', '71'])).
% 0.17/0.47  thf('73', plain,
% 0.17/0.47      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('split', [status(esa)], ['19'])).
% 0.17/0.47  thf('74', plain,
% 0.17/0.47      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.17/0.47         | ((sk_A) = (k1_xboole_0))
% 0.17/0.47         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47         | ((sk_C) = (k1_xboole_0))))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['72', '73'])).
% 0.17/0.47  thf('75', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.17/0.47      inference('sup-', [status(thm)], ['58', '59'])).
% 0.17/0.47  thf('76', plain,
% 0.17/0.47      (((((sk_A) = (k1_xboole_0))
% 0.17/0.47         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47         | ((sk_C) = (k1_xboole_0))))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('demod', [status(thm)], ['74', '75'])).
% 0.17/0.47  thf('77', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.17/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.17/0.47  thf('78', plain,
% 0.17/0.47      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.47         | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47         | ((sk_A) = (k1_xboole_0))
% 0.17/0.47         | (v1_xboole_0 @ sk_F)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['76', '77'])).
% 0.17/0.47  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('80', plain,
% 0.17/0.47      (((((sk_B_1) = (k1_xboole_0))
% 0.17/0.47         | ((sk_A) = (k1_xboole_0))
% 0.17/0.47         | (v1_xboole_0 @ sk_F)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('demod', [status(thm)], ['78', '79'])).
% 0.17/0.47  thf('81', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.17/0.47      inference('sup-', [status(thm)], ['48', '49'])).
% 0.17/0.47  thf('82', plain,
% 0.17/0.47      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('clc', [status(thm)], ['80', '81'])).
% 0.17/0.47  thf('83', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.17/0.47      inference('sup-', [status(thm)], ['52', '53'])).
% 0.17/0.47  thf('84', plain,
% 0.17/0.47      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.47         | ((sk_A) = (k1_xboole_0))
% 0.17/0.47         | (v1_xboole_0 @ sk_E)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['82', '83'])).
% 0.17/0.47  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('86', plain,
% 0.17/0.47      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('demod', [status(thm)], ['84', '85'])).
% 0.17/0.47  thf('87', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.17/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.17/0.47  thf('88', plain,
% 0.17/0.47      ((((sk_A) = (k1_xboole_0)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('clc', [status(thm)], ['86', '87'])).
% 0.17/0.47  thf('89', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.17/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.17/0.47  thf('90', plain,
% 0.17/0.47      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['88', '89'])).
% 0.17/0.47  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('92', plain,
% 0.17/0.47      (((v1_xboole_0 @ sk_D))
% 0.17/0.47         <= (~
% 0.17/0.47             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.17/0.47      inference('demod', [status(thm)], ['90', '91'])).
% 0.17/0.47  thf('93', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.17/0.47      inference('sup-', [status(thm)], ['8', '11'])).
% 0.17/0.47  thf('94', plain,
% 0.17/0.47      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.17/0.47      inference('sup-', [status(thm)], ['92', '93'])).
% 0.17/0.47  thf('95', plain,
% 0.17/0.47      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.17/0.47       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.17/0.47       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.17/0.47      inference('split', [status(esa)], ['19'])).
% 0.17/0.47  thf('96', plain,
% 0.17/0.47      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.17/0.47      inference('sat_resolution*', [status(thm)], ['69', '94', '95'])).
% 0.17/0.47  thf('97', plain,
% 0.17/0.47      (~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)),
% 0.17/0.47      inference('simpl_trail', [status(thm)], ['20', '96'])).
% 0.17/0.47  thf('98', plain,
% 0.17/0.47      ((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.17/0.47        | ((sk_A) = (k1_xboole_0))
% 0.17/0.47        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47        | ((sk_C) = (k1_xboole_0)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['18', '97'])).
% 0.17/0.47  thf('99', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.17/0.47      inference('sup-', [status(thm)], ['44', '47'])).
% 0.17/0.47  thf('100', plain,
% 0.17/0.47      ((((sk_A) = (k1_xboole_0))
% 0.17/0.47        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47        | ((sk_C) = (k1_xboole_0)))),
% 0.17/0.47      inference('demod', [status(thm)], ['98', '99'])).
% 0.17/0.47  thf('101', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.17/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.17/0.47  thf('102', plain,
% 0.17/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.47        | ((sk_B_1) = (k1_xboole_0))
% 0.17/0.47        | ((sk_A) = (k1_xboole_0))
% 0.17/0.47        | (v1_xboole_0 @ sk_F))),
% 0.17/0.47      inference('sup-', [status(thm)], ['100', '101'])).
% 0.17/0.47  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('104', plain,
% 0.17/0.47      ((((sk_B_1) = (k1_xboole_0))
% 0.17/0.47        | ((sk_A) = (k1_xboole_0))
% 0.17/0.47        | (v1_xboole_0 @ sk_F))),
% 0.17/0.47      inference('demod', [status(thm)], ['102', '103'])).
% 0.17/0.47  thf('105', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.17/0.47      inference('sup-', [status(thm)], ['48', '49'])).
% 0.17/0.47  thf('106', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.17/0.47      inference('clc', [status(thm)], ['104', '105'])).
% 0.17/0.47  thf('107', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.17/0.47      inference('sup-', [status(thm)], ['52', '53'])).
% 0.17/0.47  thf('108', plain,
% 0.17/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.17/0.47        | ((sk_A) = (k1_xboole_0))
% 0.17/0.47        | (v1_xboole_0 @ sk_E))),
% 0.17/0.47      inference('sup-', [status(thm)], ['106', '107'])).
% 0.17/0.47  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('110', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.17/0.47      inference('demod', [status(thm)], ['108', '109'])).
% 0.17/0.47  thf('111', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.17/0.47      inference('sup-', [status(thm)], ['60', '61'])).
% 0.17/0.47  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 0.17/0.47      inference('clc', [status(thm)], ['110', '111'])).
% 0.17/0.47  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.17/0.47  thf('114', plain, ((v1_xboole_0 @ sk_D)),
% 0.17/0.47      inference('demod', [status(thm)], ['15', '112', '113'])).
% 0.17/0.47  thf('115', plain, ($false), inference('demod', [status(thm)], ['12', '114'])).
% 0.17/0.47  
% 0.17/0.47  % SZS output end Refutation
% 0.17/0.47  
% 0.17/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
