%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPhiNXLI1P

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:06 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 547 expanded)
%              Number of leaves         :   33 ( 188 expanded)
%              Depth                    :   19
%              Number of atoms          : 1254 (6088 expanded)
%              Number of equality atoms :   75 ( 106 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
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

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_F )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['40','49'])).

thf('51',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('65',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('73',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('75',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['40','49'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('80',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('82',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('84',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('92',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('96',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('98',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('99',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('102',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['32'])).

thf('104',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['40','49'])).

thf('107',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('109',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('111',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('113',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('117',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('121',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['32'])).

thf('123',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['96','121','122'])).

thf('124',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['65','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('126',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('128',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['21','126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['12','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hPhiNXLI1P
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 288 iterations in 0.144s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.61  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.42/0.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.42/0.61  thf(sk_G_type, type, sk_G: $i).
% 0.42/0.61  thf(d1_xboole_0, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.61  thf(t10_mcart_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.42/0.61       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.42/0.61         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.42/0.61          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.42/0.61          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(d3_zfmisc_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.42/0.61       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.61         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.42/0.61           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.61          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['4', '7'])).
% 0.42/0.61  thf(t76_mcart_1, conjecture,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ![E:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.42/0.61           ( ![F:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.42/0.61               ( ![G:$i]:
% 0.42/0.61                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.42/0.61                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.42/0.61                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.42/0.61                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.42/0.61                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61          ( ![E:$i]:
% 0.42/0.61            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.42/0.61              ( ![F:$i]:
% 0.42/0.61                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.42/0.61                  ( ![G:$i]:
% 0.42/0.61                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.42/0.61                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.42/0.61                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.42/0.61                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.42/0.61                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.42/0.61  thf('9', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.61  thf('11', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.61  thf('12', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('sup-', [status(thm)], ['8', '11'])).
% 0.42/0.61  thf('13', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i]:
% 0.42/0.61         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('15', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.42/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.42/0.61  thf(t3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.42/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.42/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.42/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf(t69_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i]:
% 0.42/0.62         (~ (r1_xboole_0 @ X8 @ X9)
% 0.42/0.62          | ~ (r1_tarski @ X8 @ X9)
% 0.42/0.62          | (v1_xboole_0 @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('21', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '20'])).
% 0.42/0.62  thf('22', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.42/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.62          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.42/0.62      inference('sup-', [status(thm)], ['22', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.62  thf('28', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.42/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t50_mcart_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62          ( ~( ![D:$i]:
% 0.42/0.62               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.42/0.62                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.42/0.62                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.42/0.62                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.42/0.62                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.42/0.62                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.62         (((X21) = (k1_xboole_0))
% 0.42/0.62          | ((X22) = (k1_xboole_0))
% 0.42/0.62          | ((k6_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.42/0.62              = (k2_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.42/0.62          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.42/0.62          | ((X24) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.42/0.62            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.42/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)
% 0.42/0.62        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)
% 0.42/0.62        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('split', [status(esa)], ['32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_C_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['31', '33'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['28', '34'])).
% 0.42/0.62  thf('36', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('38', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('40', plain, (((v1_xboole_0 @ sk_F) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.42/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.42/0.62          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['41', '46'])).
% 0.42/0.62  thf('48', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('49', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.42/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('50', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.42/0.62      inference('clc', [status(thm)], ['40', '49'])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '50'])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('52', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.62  thf(t7_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (![X13 : $i, X14 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.62  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('demod', [status(thm)], ['51', '56'])).
% 0.42/0.62  thf('58', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X10 : $i, X11 : $i]:
% 0.42/0.62         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.62  thf('60', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1) | ~ (r1_tarski @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.62  thf('62', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['57', '62'])).
% 0.42/0.62  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.42/0.62      inference('demod', [status(thm)], ['63', '64'])).
% 0.42/0.62  thf('66', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('67', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.42/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.42/0.62  thf('68', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.62          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.42/0.62  thf('70', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.42/0.62      inference('sup-', [status(thm)], ['66', '69'])).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.62         (((X21) = (k1_xboole_0))
% 0.42/0.62          | ((X22) = (k1_xboole_0))
% 0.42/0.62          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.42/0.62          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.42/0.62          | ((X24) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.42/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.42/0.62  thf('74', plain,
% 0.42/0.62      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('split', [status(esa)], ['32'])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_C_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['70', '75'])).
% 0.42/0.62  thf('77', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.42/0.62      inference('clc', [status(thm)], ['40', '49'])).
% 0.42/0.62  thf('78', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.42/0.62  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.62  thf('81', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('82', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.42/0.62  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('84', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('demod', [status(thm)], ['82', '83'])).
% 0.42/0.62  thf('85', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.62  thf('86', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.42/0.62          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.42/0.62      inference('sup+', [status(thm)], ['5', '6'])).
% 0.42/0.62  thf('87', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.42/0.62  thf('88', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.42/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('89', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.42/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['84', '89'])).
% 0.42/0.62  thf('91', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '20'])).
% 0.42/0.62  thf('92', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['90', '91'])).
% 0.42/0.62  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('94', plain,
% 0.42/0.62      (((v1_xboole_0 @ sk_D))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.42/0.62      inference('demod', [status(thm)], ['92', '93'])).
% 0.42/0.62  thf('95', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '11'])).
% 0.42/0.62  thf('96', plain,
% 0.42/0.62      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.42/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.42/0.62  thf('97', plain,
% 0.42/0.62      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.42/0.62      inference('sup-', [status(thm)], ['22', '25'])).
% 0.42/0.62  thf('98', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.42/0.62          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.62  thf('99', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.42/0.62      inference('sup-', [status(thm)], ['97', '98'])).
% 0.42/0.62  thf('100', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('101', plain,
% 0.42/0.62      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.62         (((X21) = (k1_xboole_0))
% 0.42/0.62          | ((X22) = (k1_xboole_0))
% 0.42/0.62          | ((k5_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.42/0.62              = (k1_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.42/0.62          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.42/0.62          | ((X24) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.42/0.62  thf('102', plain,
% 0.42/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G)
% 0.42/0.62            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.42/0.62        | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['100', '101'])).
% 0.42/0.62  thf('103', plain,
% 0.42/0.62      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('split', [status(esa)], ['32'])).
% 0.42/0.62  thf('104', plain,
% 0.42/0.62      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_C_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['102', '103'])).
% 0.42/0.62  thf('105', plain,
% 0.42/0.62      (((((sk_C_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['99', '104'])).
% 0.42/0.62  thf('106', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.42/0.62      inference('clc', [status(thm)], ['40', '49'])).
% 0.42/0.62  thf('107', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['105', '106'])).
% 0.42/0.62  thf('108', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('109', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('demod', [status(thm)], ['107', '108'])).
% 0.42/0.62  thf('110', plain, (((v1_xboole_0 @ sk_E) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('111', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.42/0.62  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('113', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.42/0.62  thf('114', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.42/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf('115', plain,
% 0.42/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('clc', [status(thm)], ['113', '114'])).
% 0.42/0.62  thf('116', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '20'])).
% 0.42/0.62  thf('117', plain,
% 0.42/0.62      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.42/0.62  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('119', plain,
% 0.42/0.62      (((v1_xboole_0 @ sk_D))
% 0.42/0.62         <= (~
% 0.42/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.42/0.62      inference('demod', [status(thm)], ['117', '118'])).
% 0.42/0.62  thf('120', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.62      inference('sup-', [status(thm)], ['8', '11'])).
% 0.42/0.62  thf('121', plain,
% 0.42/0.62      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D))),
% 0.42/0.62      inference('sup-', [status(thm)], ['119', '120'])).
% 0.42/0.62  thf('122', plain,
% 0.42/0.62      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.42/0.62       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.42/0.62       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_F))),
% 0.42/0.62      inference('split', [status(esa)], ['32'])).
% 0.42/0.62  thf('123', plain,
% 0.42/0.62      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_G) @ sk_E))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['96', '121', '122'])).
% 0.42/0.62  thf('124', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['65', '123'])).
% 0.42/0.62  thf('125', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.42/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.42/0.62  thf('126', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.62      inference('clc', [status(thm)], ['124', '125'])).
% 0.42/0.62  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.62      inference('sup-', [status(thm)], ['52', '55'])).
% 0.42/0.62  thf('128', plain, ((v1_xboole_0 @ sk_D)),
% 0.42/0.62      inference('demod', [status(thm)], ['21', '126', '127'])).
% 0.42/0.62  thf('129', plain, ($false), inference('demod', [status(thm)], ['12', '128'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
