%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MlvxfJ4zb1

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 446 expanded)
%              Number of leaves         :   31 ( 150 expanded)
%              Depth                    :   21
%              Number of atoms          : 1187 (5449 expanded)
%              Number of equality atoms :   75 ( 124 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
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
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
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

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X24 @ X25 @ X27 @ X26 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('28',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X21 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_F @ ( k1_zfmisc_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    r2_hidden @ sk_F @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('44',plain,(
    r1_tarski @ sk_F @ sk_C_2 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['32','49'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    r2_hidden @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('60',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( sk_B @ sk_E ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X24 @ X25 @ X27 @ X26 )
        = ( k2_mcart_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('71',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['29'])).

thf('73',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['33','36'])).

thf('75',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('77',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('81',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['23','24'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('89',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('93',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('95',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X24 @ X25 @ X27 @ X26 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X24 @ X25 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('97',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['29'])).

thf('99',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( sk_C_2 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('102',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('106',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('110',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('112',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('116',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['29'])).

thf('118',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['93','116','117'])).

thf('119',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['68','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('121',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['22','121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['8','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MlvxfJ4zb1
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:29:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 251 iterations in 0.093s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.55  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(t76_mcart_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ![E:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.55           ( ![F:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.55               ( ![G:$i]:
% 0.21/0.55                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.55                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.55                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.55                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.55                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ![E:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.55              ( ![F:$i]:
% 0.21/0.55                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.55                  ( ![G:$i]:
% 0.21/0.55                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.55                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.55                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.55                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.55                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.21/0.55  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d3_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.55         ((k3_zfmisc_1 @ X18 @ X19 @ X20)
% 0.21/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.55  thf(t10_mcart_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.21/0.55          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         ((r2_hidden @ (k1_mcart_1 @ X21) @ X22)
% 0.21/0.55          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.55  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(d1_xboole_0, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('8', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('10', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t2_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((r2_hidden @ X14 @ X15)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('13', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('14', plain, ((r2_hidden @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X11 @ X10)
% 0.21/0.55          | (r1_tarski @ X11 @ X9)
% 0.21/0.55          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X9 : $i, X11 : $i]:
% 0.21/0.55         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('17', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.55          | (r2_hidden @ X3 @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_B @ sk_D) @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('22', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 0.21/0.55          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.55  thf('25', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t50_mcart_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.55          ( ~( ![D:$i]:
% 0.21/0.55               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.55                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.55                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.55                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.55         (((X24) = (k1_xboole_0))
% 0.21/0.55          | ((X25) = (k1_xboole_0))
% 0.21/0.55          | ((k6_mcart_1 @ X24 @ X25 @ X27 @ X26)
% 0.21/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X26)))
% 0.21/0.55          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X24 @ X25 @ X27))
% 0.21/0.55          | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.21/0.55        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 0.21/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)
% 0.21/0.55        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)
% 0.21/0.55        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('split', [status(esa)], ['29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['28', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((((sk_C_2) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '31'])).
% 0.21/0.55  thf('33', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.55         ((k3_zfmisc_1 @ X18 @ X19 @ X20)
% 0.21/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         ((r2_hidden @ (k2_mcart_1 @ X21) @ X23)
% 0.21/0.55          | ~ (r2_hidden @ X21 @ (k2_zfmisc_1 @ X22 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.55  thf('38', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_2))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((r2_hidden @ X14 @ X15)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_C_2))
% 0.21/0.55        | (r2_hidden @ sk_F @ (k1_zfmisc_1 @ sk_C_2)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.55  thf('41', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('42', plain, ((r2_hidden @ sk_F @ (k1_zfmisc_1 @ sk_C_2))),
% 0.21/0.55      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X9 : $i, X11 : $i]:
% 0.21/0.55         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('44', plain, ((r1_tarski @ sk_F @ sk_C_2)),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.55          | (r2_hidden @ X3 @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_2)),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '46'])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('49', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '49'])).
% 0.21/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.55  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('54', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         ((r2_hidden @ X14 @ X15)
% 0.21/0.55          | (v1_xboole_0 @ X15)
% 0.21/0.55          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.55        | (r2_hidden @ sk_E @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('58', plain, ((r2_hidden @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.55      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X9 : $i, X11 : $i]:
% 0.21/0.55         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.55  thf('60', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.55          | (r2_hidden @ X3 @ X5)
% 0.21/0.55          | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.21/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_E) | (r2_hidden @ (sk_B @ sk_E) @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('65', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '65'])).
% 0.21/0.55  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.21/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.55         (((X24) = (k1_xboole_0))
% 0.21/0.55          | ((X25) = (k1_xboole_0))
% 0.21/0.55          | ((k7_mcart_1 @ X24 @ X25 @ X27 @ X26) = (k2_mcart_1 @ X26))
% 0.21/0.55          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X24 @ X25 @ X27))
% 0.21/0.55          | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.21/0.55        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.21/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('split', [status(esa)], ['29'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.55  thf('74', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.55  thf('76', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.55  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('79', plain,
% 0.21/0.55      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.55  thf('80', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.55  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.55  thf('84', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.55  thf('86', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('87', plain,
% 0.21/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['83', '86'])).
% 0.21/0.55  thf('88', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('89', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.55  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_D))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.21/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.55  thf('92', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('93', plain,
% 0.21/0.55      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.21/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.55  thf('94', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('95', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('96', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.55         (((X24) = (k1_xboole_0))
% 0.21/0.55          | ((X25) = (k1_xboole_0))
% 0.21/0.55          | ((k5_mcart_1 @ X24 @ X25 @ X27 @ X26)
% 0.21/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ X26)))
% 0.21/0.55          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X24 @ X25 @ X27))
% 0.21/0.55          | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.55  thf('97', plain,
% 0.21/0.55      ((((sk_C_2) = (k1_xboole_0))
% 0.21/0.55        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 0.21/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.21/0.55  thf('98', plain,
% 0.21/0.55      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('split', [status(esa)], ['29'])).
% 0.21/0.55  thf('99', plain,
% 0.21/0.55      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_C_2) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.55  thf('100', plain,
% 0.21/0.55      (((((sk_C_2) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['94', '99'])).
% 0.21/0.55  thf('101', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.21/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.55  thf('102', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.55  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('104', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.55  thf('105', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.55  thf('106', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.55         | ((sk_A) = (k1_xboole_0))
% 0.21/0.55         | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.55  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('108', plain,
% 0.21/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.55  thf('109', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('110', plain,
% 0.21/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.55  thf('111', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('112', plain,
% 0.21/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.55  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('114', plain,
% 0.21/0.55      (((v1_xboole_0 @ sk_D))
% 0.21/0.55         <= (~
% 0.21/0.55             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.21/0.55      inference('demod', [status(thm)], ['112', '113'])).
% 0.21/0.55  thf('115', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('116', plain,
% 0.21/0.55      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))),
% 0.21/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.55  thf('117', plain,
% 0.21/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)) | 
% 0.21/0.55       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)) | 
% 0.21/0.55       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.21/0.55      inference('split', [status(esa)], ['29'])).
% 0.21/0.55  thf('118', plain,
% 0.21/0.55      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['93', '116', '117'])).
% 0.21/0.55  thf('119', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['68', '118'])).
% 0.21/0.55  thf('120', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.21/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('121', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.55  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.55  thf('123', plain, ((v1_xboole_0 @ sk_D)),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '121', '122'])).
% 0.21/0.55  thf('124', plain, ($false), inference('demod', [status(thm)], ['8', '123'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
