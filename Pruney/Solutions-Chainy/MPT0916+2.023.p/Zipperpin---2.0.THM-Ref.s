%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSivpoFll2

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:08 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 454 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :   21
%              Number of atoms          : 1039 (6591 expanded)
%              Number of equality atoms :   69 ( 120 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_A ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2 ) ),
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

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','30'])).

thf('34',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_F @ sk_C_2 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','30'])).

thf('41',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('45',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('46',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('49',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['47','48'])).

thf('57',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( ~ ( r1_xboole_0 @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('64',plain,
    ( ~ ( r1_xboole_0 @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('66',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('69',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('71',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('73',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('75',plain,
    ( ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('77',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('79',plain,
    ( ( ~ ( r1_xboole_0 @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('83',plain,
    ( ~ ( r1_xboole_0 @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('85',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('87',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['66','85','86'])).

thf('88',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['21','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','88'])).

thf('90',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['47','48'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('93',plain,
    ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('97',plain,
    ( ~ ( r1_xboole_0 @ sk_E @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['16','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NSivpoFll2
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 324 iterations in 0.101s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.55  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.55  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.37/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.55  thf(t76_mcart_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55       ( ![E:$i]:
% 0.37/0.55         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.55           ( ![F:$i]:
% 0.37/0.55             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.55               ( ![G:$i]:
% 0.37/0.55                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.37/0.55                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.37/0.55                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.37/0.55                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.55          ( ![E:$i]:
% 0.37/0.55            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.55              ( ![F:$i]:
% 0.37/0.55                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.55                  ( ![G:$i]:
% 0.37/0.55                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.37/0.55                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.37/0.55                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.37/0.55                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.37/0.55  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(d3_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.37/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.37/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.55  thf(t10_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.37/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.37/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.37/0.55          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.37/0.55          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t3_subset, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('9', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.55  thf(d3_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.37/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '11'])).
% 0.37/0.55  thf('13', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf(t3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.55          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain, (~ (r1_xboole_0 @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t50_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ~( ![D:$i]:
% 0.37/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.37/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.37/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.37/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.37/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.37/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.55         (((X18) = (k1_xboole_0))
% 0.37/0.55          | ((X19) = (k1_xboole_0))
% 0.37/0.55          | ((k6_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.37/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.37/0.55          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.37/0.55          | ((X21) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.37/0.55        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G)
% 0.37/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)
% 0.37/0.55        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E)
% 0.37/0.55        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.37/0.55      inference('split', [status(esa)], ['20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.55         (((X18) = (k1_xboole_0))
% 0.37/0.55          | ((X19) = (k1_xboole_0))
% 0.37/0.55          | ((k7_mcart_1 @ X18 @ X19 @ X21 @ X20) = (k2_mcart_1 @ X20))
% 0.37/0.55          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.37/0.55          | ((X21) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.37/0.55        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('split', [status(esa)], ['20'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.37/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.37/0.55          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['26', '31'])).
% 0.37/0.55  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.37/0.55  thf('34', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('36', plain, ((r1_tarski @ sk_F @ sk_C_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('38', plain,
% 0.37/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.55  thf('39', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['33', '38'])).
% 0.37/0.55  thf('40', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.55          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_F @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('43', plain, (~ (r1_xboole_0 @ sk_F @ sk_C_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (((~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '43'])).
% 0.37/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.55  thf('45', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.37/0.55          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('49', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('51', plain,
% 0.37/0.55      (![X9 : $i, X10 : $i]:
% 0.37/0.55         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.55  thf('52', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ X0 @ X2)
% 0.37/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.55  thf('55', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '54'])).
% 0.37/0.55  thf('56', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('57', plain,
% 0.37/0.55      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X6 @ X4)
% 0.37/0.55          | ~ (r2_hidden @ X6 @ X7)
% 0.37/0.55          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('58', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ sk_E @ X0)
% 0.37/0.55          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain, (~ (r1_xboole_0 @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (((~ (r1_xboole_0 @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['46', '59'])).
% 0.37/0.55  thf('61', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('62', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.37/0.55  thf('63', plain, (~ (r1_xboole_0 @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ sk_D @ k1_xboole_0))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.55  thf('65', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F))),
% 0.37/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.55         (((X18) = (k1_xboole_0))
% 0.37/0.55          | ((X19) = (k1_xboole_0))
% 0.37/0.55          | ((k5_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.37/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.37/0.55          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.37/0.55          | ((X21) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.37/0.55  thf('69', plain,
% 0.37/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.37/0.55        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G)
% 0.37/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.37/0.55  thf('70', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('split', [status(esa)], ['20'])).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.55  thf('72', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.37/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.55  thf('73', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.37/0.55  thf('74', plain, (~ (r1_xboole_0 @ sk_F @ sk_C_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (((~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 0.37/0.55         | ((sk_B) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.37/0.55  thf('76', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('77', plain,
% 0.37/0.55      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('78', plain, (~ (r1_xboole_0 @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.55  thf('79', plain,
% 0.37/0.55      (((~ (r1_xboole_0 @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.55  thf('80', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('81', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('82', plain, (~ (r1_xboole_0 @ sk_D @ sk_A)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('83', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ sk_D @ k1_xboole_0))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.55  thf('84', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D))),
% 0.37/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E)) | 
% 0.37/0.55       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_D)) | 
% 0.37/0.55       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_F))),
% 0.37/0.55      inference('split', [status(esa)], ['20'])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['66', '85', '86'])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_2 @ sk_G) @ sk_E)),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['21', '87'])).
% 0.37/0.55  thf('89', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '88'])).
% 0.37/0.55  thf('90', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('91', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.37/0.55  thf('92', plain, (~ (r1_xboole_0 @ sk_F @ sk_C_2)),
% 0.37/0.55      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.55  thf('93', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 0.37/0.55        | ((sk_B) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.37/0.55  thf('94', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('95', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.37/0.55  thf('96', plain, (~ (r1_xboole_0 @ sk_E @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.55  thf('97', plain,
% 0.37/0.55      ((~ (r1_xboole_0 @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.37/0.55  thf('98', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['97', '98'])).
% 0.37/0.55  thf('100', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.55  thf('101', plain, ($false),
% 0.37/0.55      inference('demod', [status(thm)], ['16', '99', '100'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
