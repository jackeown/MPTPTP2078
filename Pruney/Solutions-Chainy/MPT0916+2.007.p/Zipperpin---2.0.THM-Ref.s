%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D90wWt2RxF

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  202 (6251 expanded)
%              Number of leaves         :   30 (1818 expanded)
%              Depth                    :   45
%              Number of atoms          : 1846 (108735 expanded)
%              Number of equality atoms :  237 (5227 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['16'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_F )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['45'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_E )
    | ( sk_B_1 = sk_E ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf('57',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['56'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_D )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['30','33'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('76',plain,
    ( ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F ) )
      | ( k1_xboole_0 = sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['24','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('86',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['16'])).

thf('88',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('91',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('95',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('97',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('98',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_F )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('99',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('101',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('105',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_E )
    | ( sk_B_1 = sk_E ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('106',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('108',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simplify,[status(thm)],['109'])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_D )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('113',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('115',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( sk_A = sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( ( k1_xboole_0 = sk_F )
      | ( k1_xboole_0 = sk_E )
      | ( k1_xboole_0 = sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('119',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('121',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ( k1_xboole_0 = sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('129',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['16'])).

thf('133',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['83','131','132'])).

thf('134',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['17','133'])).

thf('135',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','134'])).

thf('136',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('137',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('138',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('140',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','138'])).

thf('141',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_F )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('142',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_F )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('144',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C = sk_F ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F ) ),
    inference(simplify,[status(thm)],['145'])).

thf('148',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_E )
    | ( sk_B_1 = sk_E ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('149',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = sk_E ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('151',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = sk_E ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F ) ),
    inference('sup+',[status(thm)],['146','151'])).

thf('153',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference(simplify,[status(thm)],['152'])).

thf('155',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_D )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('156',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('158',plain,
    ( ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( sk_A = sk_D ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E ) ),
    inference('sup+',[status(thm)],['153','158'])).

thf('160',plain,
    ( ( k1_xboole_0 = sk_F )
    | ( k1_xboole_0 = sk_E )
    | ( k1_xboole_0 = sk_D ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('162',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_D )
    | ( k1_xboole_0 = sk_E ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('164',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( k1_xboole_0 = sk_E ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('166',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_D ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('168',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('170',plain,(
    $false ),
    inference(demod,[status(thm)],['12','168','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D90wWt2RxF
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 160 iterations in 0.079s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(d1_xboole_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf(t10_mcart_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.36/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.36/0.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.36/0.54          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.36/0.54          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(d3_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.54          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.36/0.54  thf(t76_mcart_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54       ( ![E:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.36/0.54           ( ![F:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.36/0.54               ( ![G:$i]:
% 0.36/0.54                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.54                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.36/0.54                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.36/0.54                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.36/0.54                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.54          ( ![E:$i]:
% 0.36/0.54            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.36/0.54              ( ![F:$i]:
% 0.36/0.54                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.36/0.54                  ( ![G:$i]:
% 0.36/0.54                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.54                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.36/0.54                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.36/0.54                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.36/0.54                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.36/0.54  thf('9', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('11', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t50_mcart_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ~( ![D:$i]:
% 0.36/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.36/0.54                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.36/0.54                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.36/0.54                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.36/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.36/0.54                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         (((X16) = (k1_xboole_0))
% 0.36/0.54          | ((X17) = (k1_xboole_0))
% 0.36/0.54          | ((k6_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.36/0.54              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.36/0.54          | ((X19) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      ((((sk_C) = (k1_xboole_0))
% 0.36/0.54        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.36/0.54            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.36/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.36/0.54        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.36/0.54        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.36/0.54          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.36/0.54          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.54          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         (((X16) = (k1_xboole_0))
% 0.36/0.54          | ((X17) = (k1_xboole_0))
% 0.36/0.54          | ((k7_mcart_1 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.36/0.54          | ((X19) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      ((((sk_C) = (k1_xboole_0))
% 0.36/0.54        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.36/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.36/0.54          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.54          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '33'])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['29', '34'])).
% 0.36/0.54  thf('37', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t3_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i]:
% 0.36/0.54         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('39', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.54  thf(d10_xboole_0, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X3 : $i, X5 : $i]:
% 0.36/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('41', plain, ((~ (r1_tarski @ sk_C @ sk_F) | ((sk_C) = (sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((~ (r1_tarski @ k1_xboole_0 @ sk_F)
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '41'])).
% 0.36/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.54  thf('43', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (((((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['35', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.54  thf('48', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i]:
% 0.36/0.54         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('50', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.36/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X3 : $i, X5 : $i]:
% 0.36/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('52', plain, ((~ (r1_tarski @ sk_B_1 @ sk_E) | ((sk_B_1) = (sk_E)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (((~ (r1_tarski @ k1_xboole_0 @ sk_E)
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['47', '52'])).
% 0.36/0.54  thf('54', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.54  thf('56', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_E))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['46', '55'])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.36/0.54  thf('59', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (![X7 : $i, X8 : $i]:
% 0.36/0.54         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('61', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.36/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.54  thf('62', plain,
% 0.36/0.54      (![X3 : $i, X5 : $i]:
% 0.36/0.54         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.54  thf('63', plain, ((~ (r1_tarski @ sk_A @ sk_D) | ((sk_A) = (sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_A) = (sk_D))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['58', '63'])).
% 0.36/0.54  thf('65', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.54  thf('66', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_E))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_A) = (sk_D))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.36/0.54  thf('67', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_D))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['57', '66'])).
% 0.36/0.54  thf('68', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))
% 0.36/0.54         | ((k1_xboole_0) = (sk_D))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['67'])).
% 0.36/0.54  thf('69', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '33'])).
% 0.36/0.54  thf('70', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('71', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.36/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.54  thf('72', plain,
% 0.36/0.54      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.54         | ((k1_xboole_0) = (sk_D))
% 0.36/0.54         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['68', '71'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('74', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_D)) | ((k1_xboole_0) = (sk_E))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.36/0.54  thf('75', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('76', plain,
% 0.36/0.54      (((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F))
% 0.36/0.54         | ((k1_xboole_0) = (sk_D))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.54  thf('77', plain,
% 0.36/0.54      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '76'])).
% 0.36/0.54  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('79', plain,
% 0.36/0.54      ((((k1_xboole_0) = (sk_D)))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.54  thf('80', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.54  thf('81', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.54  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('83', plain,
% 0.36/0.54      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.54  thf('84', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('85', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.54         (((X16) = (k1_xboole_0))
% 0.36/0.54          | ((X17) = (k1_xboole_0))
% 0.36/0.54          | ((k5_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.36/0.54              = (k1_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.36/0.54          | ((X19) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.36/0.54  thf('86', plain,
% 0.36/0.54      ((((sk_C) = (k1_xboole_0))
% 0.36/0.54        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.36/0.54            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.36/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.36/0.54  thf('87', plain,
% 0.36/0.54      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('split', [status(esa)], ['16'])).
% 0.36/0.54  thf('88', plain,
% 0.36/0.54      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.36/0.54  thf('89', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('90', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.36/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.54  thf('91', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.36/0.54          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.54  thf('92', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.54          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.36/0.54  thf('93', plain,
% 0.36/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.36/0.54      inference('sup-', [status(thm)], ['89', '92'])).
% 0.36/0.54  thf('94', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.36/0.54          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.54  thf('95', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.36/0.54      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.54  thf('96', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['88', '95'])).
% 0.36/0.54  thf('97', plain,
% 0.36/0.54      (((((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['88', '95'])).
% 0.36/0.54  thf('98', plain, ((~ (r1_tarski @ sk_C @ sk_F) | ((sk_C) = (sk_F)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('99', plain,
% 0.36/0.54      (((~ (r1_tarski @ k1_xboole_0 @ sk_F)
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['97', '98'])).
% 0.36/0.54  thf('100', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.54  thf('101', plain,
% 0.36/0.54      (((((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_C) = (sk_F))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['99', '100'])).
% 0.36/0.54  thf('102', plain,
% 0.36/0.54      (((((k1_xboole_0) = (sk_F))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_A) = (k1_xboole_0))
% 0.36/0.54         | ((sk_B_1) = (k1_xboole_0))))
% 0.36/0.54         <= (~
% 0.36/0.54             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['96', '101'])).
% 0.36/0.55  thf('103', plain,
% 0.36/0.55      (((((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['102'])).
% 0.36/0.55  thf('104', plain,
% 0.36/0.55      (((((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['102'])).
% 0.36/0.55  thf('105', plain, ((~ (r1_tarski @ sk_B_1 @ sk_E) | ((sk_B_1) = (sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('106', plain,
% 0.36/0.55      (((~ (r1_tarski @ k1_xboole_0 @ sk_E)
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((sk_B_1) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.36/0.55  thf('107', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('108', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((sk_B_1) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['106', '107'])).
% 0.36/0.55  thf('109', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_E))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['103', '108'])).
% 0.36/0.55  thf('110', plain,
% 0.36/0.55      (((((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['109'])).
% 0.36/0.55  thf('111', plain,
% 0.36/0.55      (((((sk_A) = (k1_xboole_0))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['109'])).
% 0.36/0.55  thf('112', plain, ((~ (r1_tarski @ sk_A @ sk_D) | ((sk_A) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.55  thf('113', plain,
% 0.36/0.55      (((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((sk_A) = (sk_D))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.36/0.55  thf('114', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('115', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_E))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((sk_A) = (sk_D))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['113', '114'])).
% 0.36/0.55  thf('116', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_D))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['110', '115'])).
% 0.36/0.55  thf('117', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_F))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))
% 0.36/0.55         | ((k1_xboole_0) = (sk_D))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['116'])).
% 0.36/0.55  thf('118', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.36/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('119', plain,
% 0.36/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.55         | ((k1_xboole_0) = (sk_D))
% 0.36/0.55         | ((k1_xboole_0) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['117', '118'])).
% 0.36/0.55  thf('120', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('121', plain,
% 0.36/0.55      (((((k1_xboole_0) = (sk_D)) | ((k1_xboole_0) = (sk_E))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['119', '120'])).
% 0.36/0.55  thf('122', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('123', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('124', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.36/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.36/0.55  thf('125', plain,
% 0.36/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D))))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['121', '124'])).
% 0.36/0.55  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('127', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_D)))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['125', '126'])).
% 0.36/0.55  thf('128', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.36/0.55  thf('129', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.36/0.55         <= (~
% 0.36/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['127', '128'])).
% 0.36/0.55  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('131', plain,
% 0.36/0.55      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['129', '130'])).
% 0.36/0.55  thf('132', plain,
% 0.36/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.36/0.55       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)) | 
% 0.36/0.55       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.36/0.55      inference('split', [status(esa)], ['16'])).
% 0.36/0.55  thf('133', plain,
% 0.36/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.36/0.55      inference('sat_resolution*', [status(thm)], ['83', '131', '132'])).
% 0.36/0.55  thf('134', plain,
% 0.36/0.55      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)),
% 0.36/0.55      inference('simpl_trail', [status(thm)], ['17', '133'])).
% 0.36/0.55  thf('135', plain,
% 0.36/0.55      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '134'])).
% 0.36/0.55  thf('136', plain,
% 0.36/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.36/0.55      inference('sup-', [status(thm)], ['89', '92'])).
% 0.36/0.55  thf('137', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.36/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.55  thf('138', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.36/0.55      inference('sup-', [status(thm)], ['136', '137'])).
% 0.36/0.55  thf('139', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['135', '138'])).
% 0.36/0.55  thf('140', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['135', '138'])).
% 0.36/0.55  thf('141', plain, ((~ (r1_tarski @ sk_C @ sk_F) | ((sk_C) = (sk_F)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('142', plain,
% 0.36/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_F)
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_C) = (sk_F)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['140', '141'])).
% 0.36/0.55  thf('143', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('144', plain,
% 0.36/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_C) = (sk_F)))),
% 0.36/0.55      inference('demod', [status(thm)], ['142', '143'])).
% 0.36/0.55  thf('145', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['139', '144'])).
% 0.36/0.55  thf('146', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['145'])).
% 0.36/0.55  thf('147', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['145'])).
% 0.36/0.55  thf('148', plain, ((~ (r1_tarski @ sk_B_1 @ sk_E) | ((sk_B_1) = (sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('149', plain,
% 0.36/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_E)
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['147', '148'])).
% 0.36/0.55  thf('150', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('151', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_B_1) = (sk_E)))),
% 0.36/0.55      inference('demod', [status(thm)], ['149', '150'])).
% 0.36/0.55  thf('152', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_E))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['146', '151'])).
% 0.36/0.55  thf('153', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['152'])).
% 0.36/0.55  thf('154', plain,
% 0.36/0.55      ((((sk_A) = (k1_xboole_0))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['152'])).
% 0.36/0.55  thf('155', plain, ((~ (r1_tarski @ sk_A @ sk_D) | ((sk_A) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.55  thf('156', plain,
% 0.36/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 0.36/0.55        | ((k1_xboole_0) = (sk_E))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((sk_A) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['154', '155'])).
% 0.36/0.55  thf('157', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.55  thf('158', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_E)) | ((k1_xboole_0) = (sk_F)) | ((sk_A) = (sk_D)))),
% 0.36/0.55      inference('demod', [status(thm)], ['156', '157'])).
% 0.36/0.55  thf('159', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_D))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E)))),
% 0.36/0.55      inference('sup+', [status(thm)], ['153', '158'])).
% 0.36/0.55  thf('160', plain,
% 0.36/0.55      ((((k1_xboole_0) = (sk_F))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E))
% 0.36/0.55        | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['159'])).
% 0.36/0.55  thf('161', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.36/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('162', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.55        | ((k1_xboole_0) = (sk_D))
% 0.36/0.55        | ((k1_xboole_0) = (sk_E)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['160', '161'])).
% 0.36/0.55  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('164', plain, ((((k1_xboole_0) = (sk_D)) | ((k1_xboole_0) = (sk_E)))),
% 0.36/0.55      inference('demod', [status(thm)], ['162', '163'])).
% 0.36/0.55  thf('165', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.36/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.36/0.55  thf('166', plain,
% 0.36/0.55      ((~ (v1_xboole_0 @ k1_xboole_0) | ((k1_xboole_0) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['164', '165'])).
% 0.36/0.55  thf('167', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('168', plain, (((k1_xboole_0) = (sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['166', '167'])).
% 0.36/0.55  thf('169', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('170', plain, ($false),
% 0.36/0.55      inference('demod', [status(thm)], ['12', '168', '169'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
