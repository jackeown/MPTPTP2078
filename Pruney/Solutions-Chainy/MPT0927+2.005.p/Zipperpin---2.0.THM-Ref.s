%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IWsxbzRHTs

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:19 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 648 expanded)
%              Number of leaves         :   32 ( 216 expanded)
%              Depth                    :   25
%              Number of atoms          : 1724 (10707 expanded)
%              Number of equality atoms :  134 ( 222 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
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
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
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
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['22'])).

thf('28',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
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
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['29','32'])).

thf('36',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_H @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('49',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_G @ sk_C_1 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('59',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('65',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    r1_tarski @ sk_F @ sk_B ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('78',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('83',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('85',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['47','50'])).

thf('87',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('89',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('91',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('93',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('97',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('101',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('103',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('106',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['22'])).

thf('108',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['63','64'])).

thf('110',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('114',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('116',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('118',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('122',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r1_tarski @ sk_A @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('124',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('126',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['22'])).

thf('128',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['80','103','126','127'])).

thf('129',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['23','128'])).

thf('130',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','129'])).

thf('131',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( r1_tarski @ sk_D @ ( k2_mcart_1 @ sk_I ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('134',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ sk_I ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( r1_tarski @ sk_C_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('138',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('140',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('142',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('144',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['18','144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IWsxbzRHTs
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 271 iterations in 0.157s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_H_type, type, sk_H: $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.63  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_I_type, type, sk_I: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.63  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.63  thf(sk_G_type, type, sk_G: $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.45/0.63  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.63  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(t87_mcart_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63       ( ![F:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.45/0.63           ( ![G:$i]:
% 0.45/0.63             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.45/0.63               ( ![H:$i]:
% 0.45/0.63                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.45/0.63                   ( ![I:$i]:
% 0.45/0.63                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.63                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.45/0.63                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.45/0.63                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.45/0.63                           ( r2_hidden @
% 0.45/0.63                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.45/0.63                           ( r2_hidden @
% 0.45/0.63                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.63        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.63          ( ![F:$i]:
% 0.45/0.63            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.45/0.63              ( ![G:$i]:
% 0.45/0.63                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.45/0.63                  ( ![H:$i]:
% 0.45/0.63                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.45/0.63                      ( ![I:$i]:
% 0.45/0.63                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.63                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.45/0.63                            ( ( r2_hidden @
% 0.45/0.63                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.45/0.63                              ( r2_hidden @
% 0.45/0.63                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.45/0.63                              ( r2_hidden @
% 0.45/0.63                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.45/0.63                              ( r2_hidden @
% 0.45/0.63                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d4_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.45/0.63       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.45/0.63           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.45/0.63  thf(t10_mcart_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.45/0.63       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.45/0.63         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.63  thf(d3_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.45/0.63       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.45/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.45/0.63        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.45/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.63  thf('11', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('13', plain, ((r1_tarski @ sk_E @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf(d3_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_A)),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '15'])).
% 0.45/0.63  thf(t7_ordinal1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t61_mcart_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.45/0.63          ( ~( ![E:$i]:
% 0.45/0.63               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.63                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.63                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.45/0.63                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.63                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.45/0.63                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.63                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.45/0.63                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (((X20) = (k1_xboole_0))
% 0.45/0.63          | ((X21) = (k1_xboole_0))
% 0.45/0.63          | ((X22) = (k1_xboole_0))
% 0.45/0.63          | ((k8_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.45/0.63              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X23))))
% 0.45/0.63          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.45/0.63          | ((X24) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      ((((sk_D) = (k1_xboole_0))
% 0.45/0.63        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I)
% 0.45/0.63            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.63        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63        | ((sk_B) = (k1_xboole_0))
% 0.45/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_E)
% 0.45/0.63        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63             sk_F)
% 0.45/0.63        | ~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63             sk_G)
% 0.45/0.63        | ~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63             sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_E))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63               sk_E)))),
% 0.45/0.63      inference('split', [status(esa)], ['22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (((X20) = (k1_xboole_0))
% 0.45/0.63          | ((X21) = (k1_xboole_0))
% 0.45/0.63          | ((X22) = (k1_xboole_0))
% 0.45/0.63          | ((k11_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.45/0.63          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.45/0.63          | ((X24) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      ((((sk_D) = (k1_xboole_0))
% 0.45/0.63        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I)
% 0.45/0.63            = (k2_mcart_1 @ sk_I))
% 0.45/0.63        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63        | ((sk_B) = (k1_xboole_0))
% 0.45/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63           sk_H))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('split', [status(esa)], ['22'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.63         ((k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16)
% 0.45/0.63           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X13 @ X14 @ X15) @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.63  thf('33', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (((((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)], ['28', '33'])).
% 0.45/0.63  thf('35', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.45/0.63      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.63  thf('36', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('38', plain, ((r1_tarski @ sk_H @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.45/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.63  thf('41', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_D)),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.63  thf('43', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '43'])).
% 0.45/0.63  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.63  thf('45', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (((((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.45/0.63           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.45/0.63          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.63  thf('51', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.45/0.63      inference('sup-', [status(thm)], ['47', '50'])).
% 0.45/0.63  thf('52', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C_1))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('54', plain, ((r1_tarski @ sk_G @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.45/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.63  thf('57', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_C_1)),
% 0.45/0.63      inference('sup-', [status(thm)], ['51', '56'])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['46', '59'])).
% 0.45/0.63  thf('61', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.45/0.63        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '7'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.45/0.63          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.45/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf('66', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i]:
% 0.45/0.63         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('68', plain, ((r1_tarski @ sk_F @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.63          | (r2_hidden @ X0 @ X2)
% 0.45/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.45/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_B)),
% 0.45/0.63      inference('sup-', [status(thm)], ['65', '70'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.63      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.63            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['62', '73'])).
% 0.45/0.63  thf('75', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      ((((sk_A) = (k1_xboole_0)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.63           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.63  thf('79', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('80', plain,
% 0.45/0.63      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H))),
% 0.45/0.63      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.63  thf('81', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (((X20) = (k1_xboole_0))
% 0.45/0.63          | ((X21) = (k1_xboole_0))
% 0.45/0.63          | ((X22) = (k1_xboole_0))
% 0.45/0.63          | ((k10_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.45/0.63              = (k2_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.45/0.63          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.45/0.63          | ((X24) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      ((((sk_D) = (k1_xboole_0))
% 0.45/0.63        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I)
% 0.45/0.63            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.45/0.63        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63        | ((sk_B) = (k1_xboole_0))
% 0.45/0.63        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.63           sk_G))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('split', [status(esa)], ['22'])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.63  thf('86', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.45/0.63      inference('sup-', [status(thm)], ['47', '50'])).
% 0.45/0.63  thf('87', plain,
% 0.45/0.63      (((((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['85', '86'])).
% 0.45/0.63  thf('88', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.45/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.63  thf('89', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.45/0.63         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.63  thf('90', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('91', plain,
% 0.45/0.63      (((((sk_C_1) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.63  thf('93', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))
% 0.45/0.63         | ((sk_B) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.45/0.63  thf('94', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('95', plain,
% 0.45/0.63      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['93', '94'])).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.63  thf('97', plain,
% 0.45/0.63      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.63            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.63         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['95', '96'])).
% 0.45/0.63  thf('98', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.63  thf('99', plain,
% 0.45/0.63      ((((sk_A) = (k1_xboole_0)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('demod', [status(thm)], ['97', '98'])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.63  thf('101', plain,
% 0.45/0.63      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.63           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ 
% 0.45/0.63               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.45/0.64  thf('102', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('103', plain,
% 0.45/0.64      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G))),
% 0.45/0.64      inference('demod', [status(thm)], ['101', '102'])).
% 0.45/0.64  thf('104', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('105', plain,
% 0.45/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.64         (((X20) = (k1_xboole_0))
% 0.45/0.64          | ((X21) = (k1_xboole_0))
% 0.45/0.64          | ((X22) = (k1_xboole_0))
% 0.45/0.64          | ((k9_mcart_1 @ X20 @ X21 @ X22 @ X24 @ X23)
% 0.45/0.64              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X23))))
% 0.45/0.64          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X24))
% 0.45/0.64          | ((X24) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.64  thf('106', plain,
% 0.45/0.64      ((((sk_D) = (k1_xboole_0))
% 0.45/0.64        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I)
% 0.45/0.64            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.64        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.45/0.64  thf('107', plain,
% 0.45/0.64      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_F))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('split', [status(esa)], ['22'])).
% 0.45/0.64  thf('108', plain,
% 0.45/0.64      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.45/0.64            sk_F)
% 0.45/0.64         | ((sk_A) = (k1_xboole_0))
% 0.45/0.64         | ((sk_B) = (k1_xboole_0))
% 0.45/0.64         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['106', '107'])).
% 0.45/0.64  thf('109', plain,
% 0.45/0.64      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.45/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.64  thf('110', plain,
% 0.45/0.64      (((((sk_A) = (k1_xboole_0))
% 0.45/0.64         | ((sk_B) = (k1_xboole_0))
% 0.45/0.64         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64         | ((sk_D) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('demod', [status(thm)], ['108', '109'])).
% 0.45/0.64  thf('111', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.45/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('112', plain,
% 0.45/0.64      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.45/0.64         | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64         | ((sk_B) = (k1_xboole_0))
% 0.45/0.64         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['110', '111'])).
% 0.45/0.64  thf('113', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('114', plain,
% 0.45/0.64      (((((sk_C_1) = (k1_xboole_0))
% 0.45/0.64         | ((sk_B) = (k1_xboole_0))
% 0.45/0.64         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('demod', [status(thm)], ['112', '113'])).
% 0.45/0.64  thf('115', plain,
% 0.45/0.64      (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('116', plain,
% 0.45/0.64      (((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.45/0.64         | ((sk_A) = (k1_xboole_0))
% 0.45/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.64  thf('117', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('118', plain,
% 0.45/0.64      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.64  thf('119', plain,
% 0.45/0.64      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.64  thf('120', plain,
% 0.45/0.64      (((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.64            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.64         | ((sk_A) = (k1_xboole_0))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.45/0.64  thf('121', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('122', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0)))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('demod', [status(thm)], ['120', '121'])).
% 0.45/0.64  thf('123', plain,
% 0.45/0.64      (~ (r1_tarski @ sk_A @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf('124', plain,
% 0.45/0.64      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.64           (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)))))
% 0.45/0.64         <= (~
% 0.45/0.64             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ 
% 0.45/0.64               sk_F)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['122', '123'])).
% 0.45/0.64  thf('125', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('126', plain,
% 0.45/0.64      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_F))),
% 0.45/0.64      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.64  thf('127', plain,
% 0.45/0.64      (~
% 0.45/0.64       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_E)) | 
% 0.45/0.64       ~
% 0.45/0.64       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_F)) | 
% 0.45/0.64       ~
% 0.45/0.64       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_G)) | 
% 0.45/0.64       ~
% 0.45/0.64       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_H))),
% 0.45/0.64      inference('split', [status(esa)], ['22'])).
% 0.45/0.64  thf('128', plain,
% 0.45/0.64      (~
% 0.45/0.64       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_E))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['80', '103', '126', '127'])).
% 0.45/0.64  thf('129', plain,
% 0.45/0.64      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_I) @ sk_E)),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['23', '128'])).
% 0.45/0.64  thf('130', plain,
% 0.45/0.64      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 0.45/0.64        | ((sk_A) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64        | ((sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '129'])).
% 0.45/0.64  thf('131', plain,
% 0.45/0.64      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('132', plain,
% 0.45/0.64      ((((sk_A) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64        | ((sk_D) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['130', '131'])).
% 0.45/0.64  thf('133', plain, (~ (r1_tarski @ sk_D @ (k2_mcart_1 @ sk_I))),
% 0.45/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('134', plain,
% 0.45/0.64      ((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ sk_I))
% 0.45/0.64        | ((sk_C_1) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['132', '133'])).
% 0.45/0.64  thf('135', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('136', plain,
% 0.45/0.64      ((((sk_C_1) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['134', '135'])).
% 0.45/0.64  thf('137', plain,
% 0.45/0.64      (~ (r1_tarski @ sk_C_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.64  thf('138', plain,
% 0.45/0.64      ((~ (r1_tarski @ k1_xboole_0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0))
% 0.45/0.64        | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['136', '137'])).
% 0.45/0.64  thf('139', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('140', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['138', '139'])).
% 0.45/0.64  thf('141', plain,
% 0.45/0.64      (~ (r1_tarski @ sk_B @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.64  thf('142', plain,
% 0.45/0.64      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.45/0.64           (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.45/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['140', '141'])).
% 0.45/0.64  thf('143', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('144', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['142', '143'])).
% 0.45/0.64  thf('145', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf('146', plain, ($false),
% 0.45/0.64      inference('demod', [status(thm)], ['18', '144', '145'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
