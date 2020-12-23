%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1fZ3QJWXEZ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 600 expanded)
%              Number of leaves         :   31 ( 200 expanded)
%              Depth                    :   25
%              Number of atoms          : 1682 (10467 expanded)
%              Number of equality atoms :  134 ( 222 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t87_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
     => ! [F: $i] :
          ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
         => ! [G: $i] :
              ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                     => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                       => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                          & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                          & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                          & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
       => ! [F: $i] :
            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                   => ! [I: $i] :
                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                       => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                         => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                            & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                            & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                            & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('19',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['20'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('34',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_D ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('39',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_C ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('59',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('70',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['20'])).

thf('77',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['43','46'])).

thf('79',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('81',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('83',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('85',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('89',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('93',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('98',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['20'])).

thf('100',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['57','58'])).

thf('102',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('104',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('106',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('108',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('114',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('116',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('118',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['20'])).

thf('120',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['72','95','118','119'])).

thf('121',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['21','120'])).

thf('122',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','121'])).

thf('123',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('124',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('126',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('128',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('130',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('134',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['16','136','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1fZ3QJWXEZ
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:40:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 140 iterations in 0.079s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(sk_I_type, type, sk_I: $i).
% 0.22/0.55  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.55  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.55  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.55  thf(sk_H_type, type, sk_H: $i).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.55  thf(t87_mcart_1, conjecture,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![F:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.22/0.55           ( ![G:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.22/0.55               ( ![H:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.22/0.55                   ( ![I:$i]:
% 0.22/0.55                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.55                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.22/0.55                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.22/0.55                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.22/0.55                           ( r2_hidden @
% 0.22/0.55                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.22/0.55                           ( r2_hidden @
% 0.22/0.55                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.55        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55          ( ![F:$i]:
% 0.22/0.55            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.22/0.55              ( ![G:$i]:
% 0.22/0.55                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.22/0.55                  ( ![H:$i]:
% 0.22/0.55                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.22/0.55                      ( ![I:$i]:
% 0.22/0.55                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.55                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.22/0.55                            ( ( r2_hidden @
% 0.22/0.55                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.22/0.55                              ( r2_hidden @
% 0.22/0.55                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.22/0.55                              ( r2_hidden @
% 0.22/0.55                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.22/0.55                              ( r2_hidden @
% 0.22/0.55                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d4_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.22/0.55       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.22/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.55  thf(t10_mcart_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.55       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.55         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.55          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.55  thf(d3_zfmisc_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.55       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.22/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.55          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.22/0.55        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('11', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(l3_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ X2)
% 0.22/0.55          | (r2_hidden @ X1 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.55  thf(t7_ordinal1, axiom,
% 0.22/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t61_mcart_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55          ( ~( ![E:$i]:
% 0.22/0.55               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.55                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.55                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.55                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.55                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.55                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.22/0.55                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (((X16) = (k1_xboole_0))
% 0.22/0.55          | ((X17) = (k1_xboole_0))
% 0.22/0.55          | ((X18) = (k1_xboole_0))
% 0.22/0.55          | ((k8_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19)
% 0.22/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X19))))
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20))
% 0.22/0.55          | ((X20) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      ((((sk_D) = (k1_xboole_0))
% 0.22/0.55        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.22/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)
% 0.22/0.55        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F)
% 0.22/0.55        | ~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55             sk_G)
% 0.22/0.55        | ~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55             sk_H))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_E)))),
% 0.22/0.55      inference('split', [status(esa)], ['20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.55         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.22/0.55           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.22/0.55          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.55  thf('26', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (((X16) = (k1_xboole_0))
% 0.22/0.55          | ((X17) = (k1_xboole_0))
% 0.22/0.55          | ((X18) = (k1_xboole_0))
% 0.22/0.55          | ((k11_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19) = (k2_mcart_1 @ X19))
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20))
% 0.22/0.55          | ((X20) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      ((((sk_D) = (k1_xboole_0))
% 0.22/0.55        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.22/0.55            = (k2_mcart_1 @ sk_I))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('split', [status(esa)], ['20'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (((((sk_D) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['26', '31'])).
% 0.22/0.55  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.55  thf('34', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ X2)
% 0.22/0.55          | (r2_hidden @ X1 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.22/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.55  thf('37', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_D)),
% 0.22/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.55  thf('39', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['32', '39'])).
% 0.22/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.55  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (((((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.55         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.22/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.22/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.55  thf('48', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ X2)
% 0.22/0.55          | (r2_hidden @ X1 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.22/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.55  thf('51', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_C)),
% 0.22/0.55      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.55  thf('53', plain, (~ (r1_tarski @ sk_C @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['42', '53'])).
% 0.22/0.55  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.22/0.55        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.22/0.55      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.55          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.55  thf('60', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('61', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ X2)
% 0.22/0.55          | (r2_hidden @ X1 @ X3)
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['59', '62'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['56', '65'])).
% 0.22/0.55  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_H)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.55  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.22/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (((X16) = (k1_xboole_0))
% 0.22/0.55          | ((X17) = (k1_xboole_0))
% 0.22/0.55          | ((X18) = (k1_xboole_0))
% 0.22/0.55          | ((k10_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19)
% 0.22/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X19)))
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20))
% 0.22/0.55          | ((X20) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      ((((sk_D) = (k1_xboole_0))
% 0.22/0.55        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.22/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('split', [status(esa)], ['20'])).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.55  thf('78', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.22/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      (((((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.55  thf('80', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.55  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (((((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.55  thf('84', plain, (~ (r1_tarski @ sk_C @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('85', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.55  thf('86', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('87', plain,
% 0.22/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.22/0.55  thf('88', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.55  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('91', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.55  thf('92', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('93', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_G)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.55  thf('94', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('95', plain,
% 0.22/0.55      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G))),
% 0.22/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.22/0.55  thf('96', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('97', plain,
% 0.22/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (((X16) = (k1_xboole_0))
% 0.22/0.55          | ((X17) = (k1_xboole_0))
% 0.22/0.55          | ((X18) = (k1_xboole_0))
% 0.22/0.55          | ((k9_mcart_1 @ X16 @ X17 @ X18 @ X20 @ X19)
% 0.22/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X19))))
% 0.22/0.55          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X20))
% 0.22/0.55          | ((X20) = (k1_xboole_0)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.55  thf('98', plain,
% 0.22/0.55      ((((sk_D) = (k1_xboole_0))
% 0.22/0.55        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.22/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.22/0.55  thf('99', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('split', [status(esa)], ['20'])).
% 0.22/0.55  thf('100', plain,
% 0.22/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.22/0.55            sk_F)
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.22/0.55  thf('101', plain,
% 0.22/0.55      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.55  thf('102', plain,
% 0.22/0.55      (((((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.55  thf('103', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('104', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.22/0.55         | ((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.55  thf('105', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('106', plain,
% 0.22/0.55      (((((sk_C) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('demod', [status(thm)], ['104', '105'])).
% 0.22/0.55  thf('107', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_C @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('108', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))
% 0.22/0.55         | ((sk_B) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.55  thf('109', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('110', plain,
% 0.22/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('demod', [status(thm)], ['108', '109'])).
% 0.22/0.55  thf('111', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('112', plain,
% 0.22/0.55      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.55  thf('113', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('114', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('demod', [status(thm)], ['112', '113'])).
% 0.22/0.55  thf('115', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.55  thf('116', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.22/0.55         <= (~
% 0.22/0.55             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.22/0.55               sk_F)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.22/0.55  thf('117', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('118', plain,
% 0.22/0.55      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F))),
% 0.22/0.55      inference('demod', [status(thm)], ['116', '117'])).
% 0.22/0.55  thf('119', plain,
% 0.22/0.55      (~ ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)) | 
% 0.22/0.55       ~ ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F)) | 
% 0.22/0.55       ~
% 0.22/0.55       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G)) | 
% 0.22/0.55       ~
% 0.22/0.55       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.22/0.55      inference('split', [status(esa)], ['20'])).
% 0.22/0.55  thf('120', plain,
% 0.22/0.55      (~ ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['72', '95', '118', '119'])).
% 0.22/0.55  thf('121', plain,
% 0.22/0.55      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['21', '120'])).
% 0.22/0.55  thf('122', plain,
% 0.22/0.55      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 0.22/0.55        | ((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_D) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '121'])).
% 0.22/0.55  thf('123', plain,
% 0.22/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.22/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.55  thf('124', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_D) = (k1_xboole_0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['122', '123'])).
% 0.22/0.55  thf('125', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('126', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.22/0.55        | ((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['124', '125'])).
% 0.22/0.55  thf('127', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('128', plain,
% 0.22/0.55      ((((sk_C) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['126', '127'])).
% 0.22/0.55  thf('129', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_C @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('130', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['128', '129'])).
% 0.22/0.55  thf('131', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('132', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.55      inference('demod', [status(thm)], ['130', '131'])).
% 0.22/0.55  thf('133', plain,
% 0.22/0.55      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.55  thf('134', plain,
% 0.22/0.55      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.55           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['132', '133'])).
% 0.22/0.55  thf('135', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('136', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['134', '135'])).
% 0.22/0.55  thf('137', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.55  thf('138', plain, ($false),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '136', '137'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
