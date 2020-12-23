%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kR5KFXkOWY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 347 expanded)
%              Number of leaves         :   29 ( 120 expanded)
%              Depth                    :   26
%              Number of atoms          : 1067 (4867 expanded)
%              Number of equality atoms :   78 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('26',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('28',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('30',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['25','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['24','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('54',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['23','54'])).

thf('56',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('57',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('58',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('59',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('61',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('79',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['56','79'])).

thf('81',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('82',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['55','80','81'])).

thf('83',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['22','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','83'])).

thf('85',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','40'])).

thf('98',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D ) ),
    inference(demod,[status(thm)],['9','96','97'])).

thf('99',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kR5KFXkOWY
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 101 iterations in 0.046s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t76_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.50           ( ![F:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.50               ( ![G:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.50                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.50                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.50                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.50                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50          ( ![E:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.50              ( ![F:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.50                  ( ![G:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.50                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.50                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.50                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.50                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf(t10_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t5_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.50          | ~ (v1_xboole_0 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.21/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.21/0.50          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.50          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t50_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ~( ![D:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((k7_mcart_1 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.21/0.50          | ((X19) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.21/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.21/0.50        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.21/0.50        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['21'])).
% 0.21/0.50  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('24', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('25', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((k5_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.21/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.21/0.50          | ((X19) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.21/0.50            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['21'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.50          | ~ (v1_xboole_0 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('37', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.50  thf('38', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.50  thf(t69_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.50          | ~ (r1_tarski @ X5 @ X6)
% 0.21/0.50          | (v1_xboole_0 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((sk_B_1) = (k1_xboole_0))
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '42'])).
% 0.21/0.50  thf('44', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.50          | ~ (v1_xboole_0 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.50  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '54'])).
% 0.21/0.50  thf('56', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('57', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('58', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((k6_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.21/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.21/0.50          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.21/0.50          | ((X19) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.21/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('split', [status(esa)], ['21'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.50  thf('64', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((sk_B_1) = (k1_xboole_0))
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['58', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ((sk_A) = (k1_xboole_0))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['57', '74'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.50  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.21/0.50         <= (~
% 0.21/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '79'])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.21/0.50       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.21/0.50       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.21/0.50      inference('split', [status(esa)], ['21'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['55', '80', '81'])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      (~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['22', '82'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      ((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '83'])).
% 0.21/0.50  thf('85', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.50      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_B_1) = (k1_xboole_0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.50      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '90'])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.50  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.50  thf('96', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '95'])).
% 0.21/0.50  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.50  thf('98', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '96', '97'])).
% 0.21/0.50  thf('99', plain, ($false), inference('sup-', [status(thm)], ['6', '98'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
