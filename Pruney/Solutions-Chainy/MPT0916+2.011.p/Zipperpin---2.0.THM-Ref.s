%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNi0Vjs6GS

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 357 expanded)
%              Number of leaves         :   31 ( 124 expanded)
%              Depth                    :   20
%              Number of atoms          :  975 (4849 expanded)
%              Number of equality atoms :   69 ( 102 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_A ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('15',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['16'])).

thf('22',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( sk_B @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( r1_tarski @ sk_B_1 @ ( sk_B @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('50',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('51',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_B_1 @ ( sk_B @ sk_E ) ) ),
    inference(clc,[status(thm)],['48','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('56',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('65',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['16'])).

thf('67',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['25','28'])).

thf('69',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('71',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('75',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['16'])).

thf('83',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['62','81','82'])).

thf('84',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['17','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','84'])).

thf('86',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['49','50'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','54'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['12','95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gNi0Vjs6GS
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 155 iterations in 0.055s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(t76_mcart_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.19/0.50           ( ![F:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.19/0.50               ( ![G:$i]:
% 0.19/0.50                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.19/0.50                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.19/0.50                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.19/0.50                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50          ( ![E:$i]:
% 0.19/0.50            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.19/0.50              ( ![F:$i]:
% 0.19/0.50                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.19/0.50                  ( ![G:$i]:
% 0.19/0.50                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.19/0.50                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.19/0.50                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.19/0.50                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.19/0.50  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d3_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf(t10_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.19/0.50          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.19/0.50          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.19/0.50          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.50  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(l3_subset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.19/0.50          | (r2_hidden @ X7 @ X9)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.50  thf('10', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '9'])).
% 0.19/0.50  thf(d1_xboole_0, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.50  thf('12', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t50_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ~( ![D:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.50         (((X18) = (k1_xboole_0))
% 0.19/0.50          | ((X19) = (k1_xboole_0))
% 0.19/0.50          | ((k6_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.19/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.19/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.19/0.50          | ((X21) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.19/0.50        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.19/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)
% 0.19/0.50        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)
% 0.19/0.50        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.19/0.50      inference('split', [status(esa)], ['16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.50         (((X18) = (k1_xboole_0))
% 0.19/0.50          | ((X19) = (k1_xboole_0))
% 0.19/0.50          | ((k5_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.19/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.19/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.19/0.50          | ((X21) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.19/0.50        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.19/0.50            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('split', [status(esa)], ['16'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.19/0.50         | ((sk_A) = (k1_xboole_0))
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_C_1) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (((((sk_A) = (k1_xboole_0))
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_C_1) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.19/0.50          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.19/0.50          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.50  thf('30', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.19/0.50          | (r2_hidden @ X7 @ X9)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.19/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.50  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['29', '32'])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.50  thf('35', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '35'])).
% 0.19/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.50  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf(d3_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i]:
% 0.19/0.50         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.50  thf('43', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.19/0.50          | (r2_hidden @ X7 @ X9)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (((v1_xboole_0 @ sk_E) | (r2_hidden @ (sk_B @ sk_E) @ sk_B_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['42', '45'])).
% 0.19/0.50  thf(t7_ordinal1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (((v1_xboole_0 @ sk_E) | ~ (r1_tarski @ sk_B_1 @ (sk_B @ sk_E)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.50         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.19/0.50          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.19/0.50  thf('51', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.50  thf('53', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.19/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.50  thf('54', plain, (~ (r1_tarski @ sk_B_1 @ (sk_B @ sk_E))),
% 0.19/0.50      inference('clc', [status(thm)], ['48', '53'])).
% 0.19/0.50  thf('55', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '55'])).
% 0.19/0.50  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['56', '57'])).
% 0.19/0.50  thf('59', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.50  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))),
% 0.19/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.50         (((X18) = (k1_xboole_0))
% 0.19/0.50          | ((X19) = (k1_xboole_0))
% 0.19/0.50          | ((k7_mcart_1 @ X18 @ X19 @ X21 @ X20) = (k2_mcart_1 @ X20))
% 0.19/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.19/0.50          | ((X21) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      ((((sk_C_1) = (k1_xboole_0))
% 0.19/0.50        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('split', [status(esa)], ['16'])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.19/0.50         | ((sk_A) = (k1_xboole_0))
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_C_1) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.50  thf('68', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (((((sk_A) = (k1_xboole_0))
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_C_1) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['67', '68'])).
% 0.19/0.50  thf('70', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('71', plain,
% 0.19/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.19/0.50  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['71', '72'])).
% 0.19/0.50  thf('74', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '54'])).
% 0.19/0.50  thf('75', plain,
% 0.19/0.50      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.19/0.50  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('77', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.50  thf('78', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.50  thf('79', plain,
% 0.19/0.50      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.19/0.50         <= (~
% 0.19/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.19/0.50  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('81', plain,
% 0.19/0.50      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.19/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.19/0.50  thf('82', plain,
% 0.19/0.50      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.19/0.50       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)) | 
% 0.19/0.50       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))),
% 0.19/0.50      inference('split', [status(esa)], ['16'])).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['62', '81', '82'])).
% 0.19/0.50  thf('84', plain,
% 0.19/0.50      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['17', '83'])).
% 0.19/0.50  thf('85', plain,
% 0.19/0.50      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.19/0.50        | ((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_C_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '84'])).
% 0.19/0.50  thf('86', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('87', plain,
% 0.19/0.50      ((((sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_C_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.50  thf('88', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('89', plain,
% 0.19/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('91', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['89', '90'])).
% 0.19/0.50  thf('92', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '54'])).
% 0.19/0.50  thf('93', plain,
% 0.19/0.50      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.19/0.50  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['93', '94'])).
% 0.19/0.50  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.50  thf('97', plain, ($false),
% 0.19/0.50      inference('demod', [status(thm)], ['12', '95', '96'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
