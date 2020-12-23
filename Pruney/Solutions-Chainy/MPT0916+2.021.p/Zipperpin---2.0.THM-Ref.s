%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eq3cPAFmOa

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 540 expanded)
%              Number of leaves         :   31 ( 179 expanded)
%              Depth                    :   25
%              Number of atoms          : 1285 (6220 expanded)
%              Number of equality atoms :   72 ( 104 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X20 @ X21 @ X23 @ X22 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('28',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
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
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X20 @ X21 @ X23 @ X22 )
        = ( k2_mcart_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('35',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('37',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['28','31'])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('50',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('60',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_zfmisc_1 @ X14 @ X15 @ X16 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['69','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['68','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['60','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('89',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','89'])).

thf('91',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('92',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('93',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X20 @ X21 @ X23 @ X22 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k3_zfmisc_1 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('95',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('97',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('100',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('102',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('104',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('106',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('112',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['91','112'])).

thf('114',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('115',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['90','113','114'])).

thf('116',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['26','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','116'])).

thf('118',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('119',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('120',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('125',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['118','119'])).

thf('127',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('135',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['21','135','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Eq3cPAFmOa
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 190 iterations in 0.135s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.40/0.62  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.40/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.40/0.62  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.62  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.40/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.40/0.62  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.62  thf(t76_mcart_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.62       ( ![E:$i]:
% 0.40/0.62         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.40/0.62           ( ![F:$i]:
% 0.40/0.62             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.40/0.62               ( ![G:$i]:
% 0.40/0.62                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.40/0.62                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.40/0.62                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.40/0.62                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.40/0.62                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.62        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.62          ( ![E:$i]:
% 0.40/0.62            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.40/0.62              ( ![F:$i]:
% 0.40/0.62                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.40/0.62                  ( ![G:$i]:
% 0.40/0.62                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.40/0.62                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.40/0.62                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.40/0.62                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.40/0.62                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.40/0.62  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(d3_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.40/0.62       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.40/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.62  thf(t10_mcart_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.40/0.62       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.40/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.40/0.62          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t3_subset, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]:
% 0.40/0.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.62  thf('9', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf(d3_tarski, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.40/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '11'])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.62  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X8 : $i, X10 : $i]:
% 0.40/0.62         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.62  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf(t5_subset, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.40/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X11 @ X12)
% 0.40/0.62          | ~ (v1_xboole_0 @ X13)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '20'])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t50_mcart_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.40/0.62          ( ~( ![D:$i]:
% 0.40/0.62               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.40/0.62                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.40/0.62                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.40/0.62                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.40/0.62                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.40/0.62                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (((X20) = (k1_xboole_0))
% 0.40/0.62          | ((X21) = (k1_xboole_0))
% 0.40/0.62          | ((k6_mcart_1 @ X20 @ X21 @ X23 @ X22)
% 0.40/0.62              = (k2_mcart_1 @ (k1_mcart_1 @ X22)))
% 0.40/0.62          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X20 @ X21 @ X23))
% 0.40/0.62          | ((X23) = (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.40/0.62        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.40/0.62            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)
% 0.40/0.62        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)
% 0.40/0.62        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.40/0.62      inference('split', [status(esa)], ['25'])).
% 0.40/0.62  thf('27', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('28', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.40/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.40/0.62          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.40/0.62  thf('32', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.40/0.62      inference('sup-', [status(thm)], ['28', '31'])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('34', plain,
% 0.40/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (((X20) = (k1_xboole_0))
% 0.40/0.62          | ((X21) = (k1_xboole_0))
% 0.40/0.62          | ((k7_mcart_1 @ X20 @ X21 @ X23 @ X22) = (k2_mcart_1 @ X22))
% 0.40/0.62          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X20 @ X21 @ X23))
% 0.40/0.62          | ((X23) = (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.40/0.62  thf('35', plain,
% 0.40/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.40/0.62        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('split', [status(esa)], ['25'])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))
% 0.40/0.62         | ((sk_C_1) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.62  thf('38', plain,
% 0.40/0.62      (((((sk_C_1) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['32', '37'])).
% 0.40/0.62  thf('39', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.40/0.62      inference('sup-', [status(thm)], ['28', '31'])).
% 0.40/0.62  thf('40', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]:
% 0.40/0.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.62  thf('42', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.40/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.62  thf('45', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['39', '44'])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('47', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('48', plain,
% 0.40/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['38', '47'])).
% 0.40/0.62  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.40/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.62  thf('50', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.62  thf(t69_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.62       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ X6 @ X7)
% 0.40/0.62          | ~ (r1_tarski @ X6 @ X7)
% 0.40/0.62          | (v1_xboole_0 @ X6))),
% 0.40/0.62      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.40/0.62  thf('52', plain,
% 0.40/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('54', plain,
% 0.40/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('demod', [status(thm)], ['48', '53'])).
% 0.40/0.62  thf('55', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('56', plain,
% 0.40/0.62      (![X8 : $i, X9 : $i]:
% 0.40/0.62         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.62  thf('57', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.62  thf('58', plain,
% 0.40/0.62      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['54', '57'])).
% 0.40/0.62  thf('59', plain,
% 0.40/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('60', plain,
% 0.40/0.62      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.62  thf('61', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('62', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('63', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.40/0.62          | (r2_hidden @ 
% 0.40/0.62             (k2_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.62  thf('64', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('65', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.40/0.62  thf('66', plain,
% 0.40/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('67', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.62  thf('68', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('69', plain,
% 0.40/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.62         ((k3_zfmisc_1 @ X14 @ X15 @ X16)
% 0.40/0.62           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15) @ X16))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.40/0.62  thf('70', plain,
% 0.40/0.62      (![X1 : $i, X3 : $i]:
% 0.40/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('71', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k1_mcart_1 @ X17) @ X18)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('72', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.40/0.62          | (r2_hidden @ 
% 0.40/0.62             (k1_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['70', '71'])).
% 0.40/0.62  thf('73', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('74', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['72', '73'])).
% 0.40/0.62  thf('75', plain,
% 0.40/0.62      (![X8 : $i, X10 : $i]:
% 0.40/0.62         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.62  thf('76', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (v1_xboole_0 @ X2)
% 0.40/0.62          | (m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['74', '75'])).
% 0.40/0.62  thf('77', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X11 @ X12)
% 0.40/0.62          | ~ (v1_xboole_0 @ X13)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.62  thf('78', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (v1_xboole_0 @ X2)
% 0.40/0.62          | ~ (v1_xboole_0 @ X0)
% 0.40/0.62          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['76', '77'])).
% 0.40/0.62  thf('79', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.62      inference('condensation', [status(thm)], ['78'])).
% 0.40/0.62  thf('80', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.40/0.62          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['69', '79'])).
% 0.40/0.62  thf('81', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.40/0.62      inference('sup-', [status(thm)], ['68', '80'])).
% 0.40/0.62  thf('82', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.40/0.62      inference('sup-', [status(thm)], ['67', '81'])).
% 0.40/0.62  thf('83', plain,
% 0.40/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['60', '82'])).
% 0.40/0.62  thf('84', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('85', plain,
% 0.40/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X11 @ X12)
% 0.40/0.62          | ~ (v1_xboole_0 @ X13)
% 0.40/0.62          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.40/0.62  thf('86', plain,
% 0.40/0.62      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.40/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.40/0.62  thf('87', plain,
% 0.40/0.62      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['83', '86'])).
% 0.40/0.62  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('89', plain,
% 0.40/0.62      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.40/0.62      inference('demod', [status(thm)], ['87', '88'])).
% 0.40/0.62  thf('90', plain,
% 0.40/0.62      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.40/0.62      inference('sup-', [status(thm)], ['27', '89'])).
% 0.40/0.62  thf('91', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('92', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.40/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.40/0.62  thf('93', plain,
% 0.40/0.62      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('94', plain,
% 0.40/0.62      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.62         (((X20) = (k1_xboole_0))
% 0.40/0.62          | ((X21) = (k1_xboole_0))
% 0.40/0.62          | ((k5_mcart_1 @ X20 @ X21 @ X23 @ X22)
% 0.40/0.62              = (k1_mcart_1 @ (k1_mcart_1 @ X22)))
% 0.40/0.62          | ~ (m1_subset_1 @ X22 @ (k3_zfmisc_1 @ X20 @ X21 @ X23))
% 0.40/0.62          | ((X23) = (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.40/0.62  thf('95', plain,
% 0.40/0.62      ((((sk_C_1) = (k1_xboole_0))
% 0.40/0.62        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.40/0.62            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['93', '94'])).
% 0.40/0.62  thf('96', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('split', [status(esa)], ['25'])).
% 0.40/0.62  thf('97', plain,
% 0.40/0.62      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))
% 0.40/0.62         | ((sk_C_1) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.40/0.62  thf('98', plain,
% 0.40/0.62      (((((sk_C_1) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['92', '97'])).
% 0.40/0.62  thf('99', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('100', plain,
% 0.40/0.62      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.62         | ((sk_A) = (k1_xboole_0))
% 0.40/0.62         | ((sk_B) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['98', '99'])).
% 0.40/0.62  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('102', plain,
% 0.40/0.62      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('demod', [status(thm)], ['100', '101'])).
% 0.40/0.62  thf('103', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.62  thf('104', plain,
% 0.40/0.62      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup+', [status(thm)], ['102', '103'])).
% 0.40/0.62  thf('105', plain,
% 0.40/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('106', plain,
% 0.40/0.62      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['104', '105'])).
% 0.40/0.62  thf('107', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.40/0.62      inference('sup-', [status(thm)], ['67', '81'])).
% 0.40/0.62  thf('108', plain,
% 0.40/0.62      ((((sk_A) = (k1_xboole_0)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('clc', [status(thm)], ['106', '107'])).
% 0.40/0.62  thf('109', plain,
% 0.40/0.62      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.40/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.40/0.62  thf('110', plain,
% 0.40/0.62      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['108', '109'])).
% 0.40/0.62  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('112', plain,
% 0.40/0.62      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.40/0.62         <= (~
% 0.40/0.62             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.40/0.62      inference('demod', [status(thm)], ['110', '111'])).
% 0.40/0.62  thf('113', plain,
% 0.40/0.62      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.40/0.62      inference('sup-', [status(thm)], ['91', '112'])).
% 0.40/0.62  thf('114', plain,
% 0.40/0.62      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.40/0.62       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.40/0.62       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.40/0.62      inference('split', [status(esa)], ['25'])).
% 0.40/0.62  thf('115', plain,
% 0.40/0.62      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['90', '113', '114'])).
% 0.40/0.62  thf('116', plain,
% 0.40/0.62      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['26', '115'])).
% 0.40/0.62  thf('117', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.40/0.62        | ((sk_A) = (k1_xboole_0))
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['24', '116'])).
% 0.40/0.62  thf('118', plain,
% 0.40/0.62      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.40/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.62  thf('119', plain,
% 0.40/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.40/0.62         ((r2_hidden @ (k2_mcart_1 @ X17) @ X19)
% 0.40/0.62          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X18 @ X19)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('120', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.40/0.62      inference('sup-', [status(thm)], ['118', '119'])).
% 0.40/0.62  thf('121', plain,
% 0.40/0.62      ((((sk_A) = (k1_xboole_0))
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['117', '120'])).
% 0.40/0.62  thf('122', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.62  thf('123', plain,
% 0.40/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.62        | ((sk_B) = (k1_xboole_0))
% 0.40/0.62        | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['121', '122'])).
% 0.40/0.62  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('125', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('demod', [status(thm)], ['123', '124'])).
% 0.40/0.62  thf('126', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.40/0.62      inference('sup-', [status(thm)], ['118', '119'])).
% 0.40/0.62  thf('127', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.62  thf('128', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.62  thf('129', plain,
% 0.40/0.62      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.40/0.62      inference('sup-', [status(thm)], ['127', '128'])).
% 0.40/0.62  thf('130', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['126', '129'])).
% 0.40/0.62  thf('131', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.62  thf('132', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['130', '131'])).
% 0.40/0.62  thf('133', plain,
% 0.40/0.62      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['125', '132'])).
% 0.40/0.62  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('135', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.62      inference('demod', [status(thm)], ['133', '134'])).
% 0.40/0.62  thf('136', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('137', plain, ($false),
% 0.40/0.62      inference('demod', [status(thm)], ['21', '135', '136'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.40/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
