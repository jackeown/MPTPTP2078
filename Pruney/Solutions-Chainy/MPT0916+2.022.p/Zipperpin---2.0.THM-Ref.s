%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3MeDsDF56u

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 382 expanded)
%              Number of leaves         :   28 ( 131 expanded)
%              Depth                    :   19
%              Number of atoms          : 1202 (5212 expanded)
%              Number of equality atoms :   73 ( 106 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

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

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ ( sk_C @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('20',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
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

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_G ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_E ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( sk_C @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_E ) )
        | ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('58',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['24'])).

thf('60',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['28','31'])).

thf('62',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('64',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_G ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( sk_C @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_E ) )
        | ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,(
    ~ ( r1_tarski @ sk_E @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ ( sk_C @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_D ) )
        | ( r1_tarski @ sk_D @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( r1_tarski @ sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('80',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('82',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('84',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['24'])).

thf('86',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('89',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_G ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_E @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( sk_C @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_E ) )
        | ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( r1_tarski @ sk_E @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r1_tarski @ sk_E @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ sk_A @ ( sk_C @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_C @ X0 @ sk_D ) )
        | ( r1_tarski @ sk_D @ X0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('101',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r1_tarski @ sk_D @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('103',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['24'])).

thf('105',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['80','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_E @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['55','105'])).

thf('107',plain,(
    ~ ( r1_tarski @ sk_E @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference(demod,[status(thm)],['17','108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['8','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3MeDsDF56u
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:31:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 195 iterations in 0.091s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.38/0.55  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.55  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.38/0.55  thf(t76_mcart_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ![E:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.38/0.55           ( ![F:$i]:
% 0.38/0.55             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.38/0.55               ( ![G:$i]:
% 0.38/0.55                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.55                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.38/0.55                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.38/0.55                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.38/0.55                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55          ( ![E:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.38/0.55              ( ![F:$i]:
% 0.38/0.55                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.38/0.55                  ( ![G:$i]:
% 0.38/0.55                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.55                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.38/0.55                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.38/0.55                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.38/0.55                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.38/0.55  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d3_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.38/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.55         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.38/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.55  thf(t10_mcart_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.38/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.38/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.38/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.38/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.38/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.38/0.55  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf(t7_ordinal1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('8', plain, (~ (r1_tarski @ sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(d3_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X1 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('10', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('12', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.55          | (r2_hidden @ X0 @ X2)
% 0.38/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.38/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ (sk_C @ X0 @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.38/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.38/0.55  thf('20', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t50_mcart_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.55          ( ~( ![D:$i]:
% 0.38/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.38/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.38/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.38/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.38/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.55         (((X16) = (k1_xboole_0))
% 0.38/0.55          | ((X17) = (k1_xboole_0))
% 0.38/0.55          | ((k6_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.38/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.38/0.55          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.38/0.55          | ((X19) = (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.38/0.55        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.38/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0))
% 0.38/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)
% 0.38/0.55        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)
% 0.38/0.55        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('split', [status(esa)], ['24'])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['23', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (((((sk_C_1) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['20', '26'])).
% 0.38/0.55  thf('28', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.55         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.38/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.38/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.38/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.55  thf('32', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.38/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.38/0.55  thf('33', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('35', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.38/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.55          | (r2_hidden @ X0 @ X2)
% 0.38/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.38/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf('38', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_1)),
% 0.38/0.55      inference('sup-', [status(thm)], ['32', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('40', plain, (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ sk_G))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_G))
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['27', '40'])).
% 0.38/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.55  thf('42', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (![X1 : $i, X3 : $i]:
% 0.38/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('45', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i]:
% 0.38/0.55         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('47', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.38/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.55          | (r2_hidden @ X0 @ X2)
% 0.38/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.38/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.38/0.55  thf('50', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_E @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_E) @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['44', '49'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_E @ X0) | ~ (r1_tarski @ sk_B @ (sk_C @ X0 @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_E))
% 0.38/0.55           | ((sk_A) = (k1_xboole_0))
% 0.38/0.55           | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['43', '52'])).
% 0.38/0.55  thf('54', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.38/0.55      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('57', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.55         (((X16) = (k1_xboole_0))
% 0.38/0.55          | ((X17) = (k1_xboole_0))
% 0.38/0.55          | ((k7_mcart_1 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.38/0.55          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.38/0.55          | ((X19) = (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.38/0.55        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0))
% 0.38/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('split', [status(esa)], ['24'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.55  thf('61', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.38/0.55      inference('sup-', [status(thm)], ['28', '31'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (((((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('63', plain, (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ sk_G))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_G))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.55  thf('65', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_E @ X0) | ~ (r1_tarski @ sk_B @ (sk_C @ X0 @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_E))
% 0.38/0.55           | ((sk_A) = (k1_xboole_0))
% 0.38/0.55           | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.55  thf('69', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('70', plain,
% 0.38/0.55      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.38/0.55  thf('71', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.38/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.55  thf('72', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.55  thf('73', plain, (~ (r1_tarski @ sk_E @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.55  thf('74', plain,
% 0.38/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['70', '73'])).
% 0.38/0.55  thf('75', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ (sk_C @ X0 @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('76', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_D))
% 0.38/0.55           | (r1_tarski @ sk_D @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.38/0.55  thf('77', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('78', plain,
% 0.38/0.55      ((![X0 : $i]: (r1_tarski @ sk_D @ X0))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.38/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.38/0.55  thf('79', plain, (~ (r1_tarski @ sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('80', plain,
% 0.38/0.55      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.38/0.55      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.55  thf('81', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.38/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.55  thf('82', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('83', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.55         (((X16) = (k1_xboole_0))
% 0.38/0.55          | ((X17) = (k1_xboole_0))
% 0.38/0.55          | ((k5_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.38/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.38/0.55          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.38/0.55          | ((X19) = (k1_xboole_0)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.38/0.55  thf('84', plain,
% 0.38/0.55      ((((sk_C_1) = (k1_xboole_0))
% 0.38/0.55        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.38/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.38/0.55        | ((sk_B) = (k1_xboole_0))
% 0.38/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.55  thf('85', plain,
% 0.38/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('split', [status(esa)], ['24'])).
% 0.38/0.55  thf('86', plain,
% 0.38/0.55      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_C_1) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.55  thf('87', plain,
% 0.38/0.55      (((((sk_C_1) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['81', '86'])).
% 0.38/0.55  thf('88', plain, (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ sk_G))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.55  thf('89', plain,
% 0.38/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_G))
% 0.38/0.55         | ((sk_A) = (k1_xboole_0))
% 0.38/0.55         | ((sk_B) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.55  thf('90', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('91', plain,
% 0.38/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.38/0.55  thf('92', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_E @ X0) | ~ (r1_tarski @ sk_B @ (sk_C @ X0 @ sk_E)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('93', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_E))
% 0.38/0.55           | ((sk_A) = (k1_xboole_0))
% 0.38/0.55           | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.38/0.55  thf('94', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('95', plain,
% 0.38/0.55      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_E @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.38/0.55  thf('96', plain, (~ (r1_tarski @ sk_E @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.55  thf('97', plain,
% 0.38/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.55  thf('98', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_A @ (sk_C @ X0 @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('99', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (~ (r1_tarski @ k1_xboole_0 @ (sk_C @ X0 @ sk_D))
% 0.38/0.55           | (r1_tarski @ sk_D @ X0)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.38/0.55  thf('100', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('101', plain,
% 0.38/0.55      ((![X0 : $i]: (r1_tarski @ sk_D @ X0))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.38/0.55      inference('demod', [status(thm)], ['99', '100'])).
% 0.38/0.55  thf('102', plain,
% 0.38/0.55      (~ (r1_tarski @ sk_D @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('103', plain,
% 0.38/0.55      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.38/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.38/0.55  thf('104', plain,
% 0.38/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.38/0.55       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.38/0.55       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.38/0.55      inference('split', [status(esa)], ['24'])).
% 0.38/0.55  thf('105', plain,
% 0.38/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['80', '103', '104'])).
% 0.38/0.55  thf('106', plain,
% 0.38/0.55      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (r1_tarski @ sk_E @ X0))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['55', '105'])).
% 0.38/0.55  thf('107', plain,
% 0.38/0.55      (~ (r1_tarski @ sk_E @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.55  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.38/0.55  thf('109', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf('110', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['17', '108', '109'])).
% 0.38/0.55  thf('111', plain, ($false), inference('demod', [status(thm)], ['8', '110'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
