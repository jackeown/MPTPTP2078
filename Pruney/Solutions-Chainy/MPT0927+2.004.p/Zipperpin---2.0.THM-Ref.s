%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wdTM8mBSAq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:19 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 728 expanded)
%              Number of leaves         :   34 ( 244 expanded)
%              Depth                    :   28
%              Number of atoms          : 2025 (11081 expanded)
%              Number of equality atoms :  145 ( 237 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
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

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('21',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('26',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['22'])).

thf('28',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['29','32'])).

thf('36',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_H @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_D ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    r1_tarski @ sk_G @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ( r2_hidden @ ( sk_B @ sk_G ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_G )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
      = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','76'])).

thf('78',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['58','81'])).

thf('83',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('84',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    r1_tarski @ sk_F @ sk_B_1 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ( r2_hidden @ ( sk_B @ sk_F ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 )
      = ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X1 @ X0 @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(clc,[status(thm)],['94','103'])).

thf('105',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( r2_hidden @ ( sk_B @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_E )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('114',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X13 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['112','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('123',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('125',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('127',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('128',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['125','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('133',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('135',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['126','129'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('138',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('143',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('145',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('146',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('148',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['143','150'])).

thf('152',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('153',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('157',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('160',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['22'])).

thf('162',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('164',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('166',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('168',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('170',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('172',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('174',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('176',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('178',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('180',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['22'])).

thf('182',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['120','157','180','181'])).

thf('183',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['23','182'])).

thf('184',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','183'])).

thf('185',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('186',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('188',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('192',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('194',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('196',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('198',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['18','198','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wdTM8mBSAq
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 267 iterations in 0.127s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.58  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.39/0.58  thf(sk_H_type, type, sk_H: $i).
% 0.39/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.58  thf(sk_I_type, type, sk_I: $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(t87_mcart_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![F:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.39/0.58           ( ![G:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.39/0.58               ( ![H:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.39/0.58                   ( ![I:$i]:
% 0.39/0.58                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.39/0.58                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.39/0.58                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.39/0.58                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.39/0.58                           ( r2_hidden @
% 0.39/0.58                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.39/0.58                           ( r2_hidden @
% 0.39/0.58                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.58        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58          ( ![F:$i]:
% 0.39/0.58            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.39/0.58              ( ![G:$i]:
% 0.39/0.58                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.39/0.58                  ( ![H:$i]:
% 0.39/0.58                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.39/0.58                      ( ![I:$i]:
% 0.39/0.58                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.39/0.58                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.39/0.58                            ( ( r2_hidden @
% 0.39/0.58                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.39/0.58                              ( r2_hidden @
% 0.39/0.58                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.39/0.58                              ( r2_hidden @
% 0.39/0.58                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.39/0.58                              ( r2_hidden @
% 0.39/0.58                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d4_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.39/0.58       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.58           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.58  thf(t10_mcart_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.39/0.58       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.39/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.58  thf(d3_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.58       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.39/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.39/0.58        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('13', plain, ((r1_tarski @ sk_E @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.58  thf(d3_tarski, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.58          | (r2_hidden @ X3 @ X5)
% 0.39/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '15'])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t61_mcart_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.39/0.58          ( ~( ![E:$i]:
% 0.39/0.58               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.39/0.58                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.39/0.58                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.39/0.58                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.39/0.58                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.39/0.58                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.39/0.58                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.39/0.58                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.58         (((X20) = (k1_xboole_0))
% 0.39/0.58          | ((X21) = (k1_xboole_0))
% 0.39/0.58          | ((X22) = (k1_xboole_0))
% 0.39/0.58          | ((k8_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.39/0.58              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X23))))
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.39/0.58          | ((X24) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((((sk_D) = (k1_xboole_0))
% 0.39/0.58        | ((k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I)
% 0.39/0.58            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.39/0.58        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58           sk_E)
% 0.39/0.58        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58             sk_F)
% 0.39/0.58        | ~ (r2_hidden @ 
% 0.39/0.58             (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)
% 0.39/0.58        | ~ (r2_hidden @ 
% 0.39/0.58             (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58           sk_E))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_E)))),
% 0.39/0.58      inference('split', [status(esa)], ['22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.58         (((X20) = (k1_xboole_0))
% 0.39/0.58          | ((X21) = (k1_xboole_0))
% 0.39/0.58          | ((X22) = (k1_xboole_0))
% 0.39/0.58          | ((k11_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.39/0.58          | ((X24) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      ((((sk_D) = (k1_xboole_0))
% 0.39/0.58        | ((k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I)
% 0.39/0.58            = (k2_mcart_1 @ sk_I))
% 0.39/0.58        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58           sk_H))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('split', [status(esa)], ['22'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.58           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.58  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (((((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('demod', [status(thm)], ['28', '33'])).
% 0.39/0.58  thf('35', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '32'])).
% 0.39/0.58  thf('36', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('38', plain, ((r1_tarski @ sk_H @ sk_D)),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.58          | (r2_hidden @ X3 @ X5)
% 0.39/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.58  thf('41', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_D)),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('43', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['34', '43'])).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (((((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('48', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('50', plain, ((r1_tarski @ sk_G @ sk_C_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.58          | (r2_hidden @ X3 @ X5)
% 0.39/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.39/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((v1_xboole_0 @ sk_G) | (r2_hidden @ (sk_B @ sk_G) @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['47', '52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('55', plain, (((v1_xboole_0 @ sk_G) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | (v1_xboole_0 @ sk_G)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '55'])).
% 0.39/0.58  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (((((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | (v1_xboole_0 @ sk_G)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.58           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.39/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.39/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.39/0.58           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.39/0.58      inference('sup+', [status(thm)], ['60', '61'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0)
% 0.39/0.58           = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['59', '62'])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.39/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.58  thf('70', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['69', '74'])).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['68', '75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['63', '76'])).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('79', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('81', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.39/0.58      inference('sup-', [status(thm)], ['77', '80'])).
% 0.39/0.58  thf('82', plain,
% 0.39/0.58      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['58', '81'])).
% 0.39/0.58  thf('83', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('84', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('86', plain, ((r1_tarski @ sk_F @ sk_B_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.39/0.58  thf('87', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.58          | (r2_hidden @ X3 @ X5)
% 0.39/0.58          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.58  thf('88', plain,
% 0.39/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.58      inference('sup-', [status(thm)], ['86', '87'])).
% 0.39/0.58  thf('89', plain,
% 0.39/0.58      (((v1_xboole_0 @ sk_F) | (r2_hidden @ (sk_B @ sk_F) @ sk_B_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['83', '88'])).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('91', plain, (((v1_xboole_0 @ sk_F) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['89', '90'])).
% 0.39/0.58  thf('92', plain,
% 0.39/0.58      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))
% 0.39/0.58         | (v1_xboole_0 @ sk_F)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['82', '91'])).
% 0.39/0.58  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('demod', [status(thm)], ['92', '93'])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.58  thf('96', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0)
% 0.39/0.58           = (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['59', '62'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['69', '74'])).
% 0.39/0.58  thf('99', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.58  thf('100', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['96', '99'])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (k4_zfmisc_1 @ X1 @ X0 @ X3 @ X2)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['95', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('103', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.39/0.58      inference('sup-', [status(thm)], ['101', '102'])).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      ((((sk_A) = (k1_xboole_0)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('clc', [status(thm)], ['94', '103'])).
% 0.39/0.58  thf('105', plain,
% 0.39/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      (((v1_xboole_0 @ sk_E) | (r2_hidden @ (sk_B @ sk_E) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['105', '106'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('109', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.58  thf('110', plain,
% 0.39/0.58      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_E)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['104', '109'])).
% 0.39/0.58  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('112', plain,
% 0.39/0.58      (((v1_xboole_0 @ sk_E))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.39/0.58      inference('demod', [status(thm)], ['110', '111'])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.39/0.58  thf('114', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.58         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.39/0.58           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.58  thf('116', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.39/0.58          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['114', '115'])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X2)
% 0.39/0.58          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['113', '116'])).
% 0.39/0.58  thf('118', plain,
% 0.39/0.58      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.58  thf('119', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.39/0.58      inference('sup-', [status(thm)], ['117', '118'])).
% 0.39/0.58  thf('120', plain,
% 0.39/0.58      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58         sk_H))),
% 0.39/0.58      inference('sup-', [status(thm)], ['112', '119'])).
% 0.39/0.58  thf('121', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('122', plain,
% 0.39/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.58         (((X20) = (k1_xboole_0))
% 0.39/0.58          | ((X21) = (k1_xboole_0))
% 0.39/0.58          | ((X22) = (k1_xboole_0))
% 0.39/0.58          | ((k10_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.39/0.58              = (k2_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.39/0.58          | ((X24) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.39/0.58  thf('123', plain,
% 0.39/0.58      ((((sk_D) = (k1_xboole_0))
% 0.39/0.58        | ((k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I)
% 0.39/0.58            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.39/0.58        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.58  thf('124', plain,
% 0.39/0.58      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.58           sk_G))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.58      inference('split', [status(esa)], ['22'])).
% 0.39/0.58  thf('125', plain,
% 0.39/0.58      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.39/0.58         | ((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['123', '124'])).
% 0.39/0.58  thf('126', plain,
% 0.39/0.58      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.58  thf('127', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.39/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.58  thf('128', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.39/0.58          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.58  thf('129', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.58          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['127', '128'])).
% 0.39/0.58  thf('130', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.39/0.58      inference('sup-', [status(thm)], ['126', '129'])).
% 0.39/0.58  thf('131', plain,
% 0.39/0.58      (((((sk_A) = (k1_xboole_0))
% 0.39/0.58         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.58         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ 
% 0.39/0.58               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.58      inference('demod', [status(thm)], ['125', '130'])).
% 0.39/0.59  thf('132', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('133', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['131', '132'])).
% 0.39/0.59  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('135', plain,
% 0.39/0.59      (((((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('demod', [status(thm)], ['133', '134'])).
% 0.39/0.59  thf('136', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.39/0.59      inference('sup-', [status(thm)], ['126', '129'])).
% 0.39/0.59  thf('137', plain,
% 0.39/0.59      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.39/0.59      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.59  thf('138', plain,
% 0.39/0.59      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['136', '137'])).
% 0.39/0.59  thf('139', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('140', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['138', '139'])).
% 0.39/0.59  thf('141', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['135', '140'])).
% 0.39/0.59  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('143', plain,
% 0.39/0.59      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('demod', [status(thm)], ['141', '142'])).
% 0.39/0.59  thf('144', plain,
% 0.39/0.59      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.39/0.59        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.39/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.39/0.59  thf('145', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.59         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.39/0.59          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.59  thf('146', plain,
% 0.39/0.59      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.39/0.59      inference('sup-', [status(thm)], ['144', '145'])).
% 0.39/0.59  thf('147', plain,
% 0.39/0.59      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.59      inference('sup-', [status(thm)], ['86', '87'])).
% 0.39/0.59  thf('148', plain,
% 0.39/0.59      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_B_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['146', '147'])).
% 0.39/0.59  thf('149', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.59  thf('150', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.59  thf('151', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['143', '150'])).
% 0.39/0.59  thf('152', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('153', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('demod', [status(thm)], ['151', '152'])).
% 0.39/0.59  thf('154', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('155', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['153', '154'])).
% 0.39/0.59  thf('156', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('157', plain,
% 0.39/0.59      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.59         sk_G))),
% 0.39/0.59      inference('demod', [status(thm)], ['155', '156'])).
% 0.39/0.59  thf('158', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('159', plain,
% 0.39/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.59         (((X20) = (k1_xboole_0))
% 0.39/0.59          | ((X21) = (k1_xboole_0))
% 0.39/0.59          | ((X22) = (k1_xboole_0))
% 0.39/0.59          | ((k9_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.39/0.59              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X23))))
% 0.39/0.59          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.39/0.59          | ((X24) = (k1_xboole_0)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.39/0.59  thf('160', plain,
% 0.39/0.59      ((((sk_D) = (k1_xboole_0))
% 0.39/0.59        | ((k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I)
% 0.39/0.59            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.39/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['158', '159'])).
% 0.39/0.59  thf('161', plain,
% 0.39/0.59      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.59           sk_F))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('split', [status(esa)], ['22'])).
% 0.39/0.59  thf('162', plain,
% 0.39/0.59      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.39/0.59            sk_F)
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['160', '161'])).
% 0.39/0.59  thf('163', plain,
% 0.39/0.59      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.39/0.59      inference('sup-', [status(thm)], ['144', '145'])).
% 0.39/0.59  thf('164', plain,
% 0.39/0.59      (((((sk_A) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_D) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('demod', [status(thm)], ['162', '163'])).
% 0.39/0.59  thf('165', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('166', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59         | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['164', '165'])).
% 0.39/0.59  thf('167', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('168', plain,
% 0.39/0.59      (((((sk_C_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('demod', [status(thm)], ['166', '167'])).
% 0.39/0.59  thf('169', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['138', '139'])).
% 0.39/0.59  thf('170', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59         | ((sk_A) = (k1_xboole_0))
% 0.39/0.59         | ((sk_B_1) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['168', '169'])).
% 0.39/0.59  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('172', plain,
% 0.39/0.59      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('demod', [status(thm)], ['170', '171'])).
% 0.39/0.59  thf('173', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.59  thf('174', plain,
% 0.39/0.59      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['172', '173'])).
% 0.39/0.59  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('176', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0)))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('demod', [status(thm)], ['174', '175'])).
% 0.39/0.59  thf('177', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.59  thf('178', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.39/0.59         <= (~
% 0.39/0.59             ((r2_hidden @ 
% 0.39/0.59               (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['176', '177'])).
% 0.39/0.59  thf('179', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('180', plain,
% 0.39/0.59      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F))),
% 0.39/0.59      inference('demod', [status(thm)], ['178', '179'])).
% 0.39/0.59  thf('181', plain,
% 0.39/0.59      (~
% 0.39/0.59       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_E)) | 
% 0.39/0.59       ~
% 0.39/0.59       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_F)) | 
% 0.39/0.59       ~
% 0.39/0.59       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.59         sk_G)) | 
% 0.39/0.59       ~
% 0.39/0.59       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.59         sk_H))),
% 0.39/0.59      inference('split', [status(esa)], ['22'])).
% 0.39/0.59  thf('182', plain,
% 0.39/0.59      (~
% 0.39/0.59       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ sk_E))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['120', '157', '180', '181'])).
% 0.39/0.59  thf('183', plain,
% 0.39/0.59      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.39/0.59          sk_E)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['23', '182'])).
% 0.39/0.59  thf('184', plain,
% 0.39/0.59      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_D) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '183'])).
% 0.39/0.59  thf('185', plain,
% 0.39/0.59      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf('186', plain,
% 0.39/0.59      ((((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_D) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['184', '185'])).
% 0.39/0.59  thf('187', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('188', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['186', '187'])).
% 0.39/0.59  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('190', plain,
% 0.39/0.59      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0))
% 0.39/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['188', '189'])).
% 0.39/0.59  thf('191', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['138', '139'])).
% 0.39/0.59  thf('192', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59        | ((sk_A) = (k1_xboole_0))
% 0.39/0.59        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['190', '191'])).
% 0.39/0.59  thf('193', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('194', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['192', '193'])).
% 0.39/0.59  thf('195', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.59      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.59  thf('196', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['194', '195'])).
% 0.39/0.59  thf('197', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('198', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.59      inference('demod', [status(thm)], ['196', '197'])).
% 0.39/0.59  thf('199', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('200', plain, ($false),
% 0.39/0.59      inference('demod', [status(thm)], ['18', '198', '199'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
