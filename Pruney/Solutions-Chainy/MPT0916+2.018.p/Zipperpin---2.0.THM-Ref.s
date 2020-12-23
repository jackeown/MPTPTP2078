%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ChIwJYfTDk

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 385 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :   27
%              Number of atoms          : 1117 (5046 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('23',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('49',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('51',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['49','54'])).

thf('56',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('57',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('66',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('69',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('72',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('74',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('76',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('78',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('80',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('84',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('88',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('90',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['61','88','89'])).

thf('91',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['16','90'])).

thf('92',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','91'])).

thf('93',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('100',plain,
    ( ( r1_tarski @ sk_F @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('104',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('106',plain,
    ( ( r1_tarski @ sk_E @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('110',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('113',plain,(
    v1_xboole_0 @ sk_D ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['8','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ChIwJYfTDk
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 105 iterations in 0.037s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(t76_mcart_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![E:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.48           ( ![F:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.48               ( ![G:$i]:
% 0.20/0.48                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.48                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.48                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.48                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48          ( ![E:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.48              ( ![F:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.48                  ( ![G:$i]:
% 0.20/0.48                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.48                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.48                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.48                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.20/0.48  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d3_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.48       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf(t10_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.48         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('8', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('11', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t50_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ![D:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((k7_mcart_1 @ X15 @ X16 @ X18 @ X17) = (k2_mcart_1 @ X17))
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.20/0.48          | ((X18) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.20/0.48        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.20/0.48        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((k5_mcart_1 @ X15 @ X16 @ X18 @ X17)
% 0.20/0.48              = (k1_mcart_1 @ (k1_mcart_1 @ X17)))
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.20/0.48          | ((X18) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.20/0.48            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('26', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.48  thf('28', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.48  thf(t69_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ X4 @ X5)
% 0.20/0.48          | ~ (r1_tarski @ X4 @ X5)
% 0.20/0.48          | (v1_xboole_0 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | (v1_xboole_0 @ sk_F)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['32', '37'])).
% 0.20/0.48  thf('39', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('41', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('clc', [status(thm)], ['31', '42'])).
% 0.20/0.48  thf('44', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('46', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['43', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('53', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('clc', [status(thm)], ['49', '54'])).
% 0.20/0.48  thf('56', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_D))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.48  thf('60', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (((X15) = (k1_xboole_0))
% 0.20/0.48          | ((X16) = (k1_xboole_0))
% 0.20/0.48          | ((k6_mcart_1 @ X15 @ X16 @ X18 @ X17)
% 0.20/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X17)))
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.20/0.48          | ((X18) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.20/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('69', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.48      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('demod', [status(thm)], ['66', '69'])).
% 0.20/0.48  thf('71', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['70', '71'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48         | (v1_xboole_0 @ sk_F)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.48  thf('75', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.48  thf('77', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['76', '77'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.48  thf('81', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.48  thf('83', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['82', '83'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_D))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.48  thf('87', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.48  thf('89', plain,
% 0.20/0.48      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.20/0.48       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.20/0.48       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['61', '88', '89'])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      (~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['16', '90'])).
% 0.20/0.48  thf('92', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.20/0.48        | ((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '91'])).
% 0.20/0.48  thf('93', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.20/0.48           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.48         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.20/0.48          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.48          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('97', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.48      inference('sup-', [status(thm)], ['93', '96'])).
% 0.20/0.48  thf('98', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['92', '97'])).
% 0.20/0.48  thf('99', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (((r1_tarski @ sk_F @ k1_xboole_0)
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['98', '99'])).
% 0.20/0.48  thf('101', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('102', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | (v1_xboole_0 @ sk_F))),
% 0.20/0.48      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.48  thf('103', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '41'])).
% 0.20/0.48  thf('104', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.48  thf('105', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      (((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['104', '105'])).
% 0.20/0.48  thf('107', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('108', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.48  thf('109', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.48  thf('110', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['108', '109'])).
% 0.20/0.48  thf('111', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '110'])).
% 0.20/0.48  thf('112', plain,
% 0.20/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('113', plain, ((v1_xboole_0 @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.48  thf('114', plain, ($false), inference('demod', [status(thm)], ['8', '113'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
