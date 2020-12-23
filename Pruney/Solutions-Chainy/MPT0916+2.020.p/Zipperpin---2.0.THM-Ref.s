%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYF6K1PJzl

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 602 expanded)
%              Number of leaves         :   31 ( 199 expanded)
%              Depth                    :   23
%              Number of atoms          : 1346 (6626 expanded)
%              Number of equality atoms :   73 ( 104 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
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
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
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
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('36',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['27','30'])).

thf('39',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('49',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X18 ) @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['59','80'])).

thf('82',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('87',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_zfmisc_1 @ X15 @ X16 @ X17 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('90',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['87','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['85','97'])).

thf('99',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('100',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('101',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('103',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('105',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('108',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('110',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('112',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('114',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('116',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('122',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['99','122'])).

thf('124',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('125',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['98','123','124'])).

thf('126',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['26','125'])).

thf('127',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','126'])).

thf('128',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('129',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X18 ) @ X20 )
      | ~ ( r2_hidden @ X18 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('130',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('133',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('135',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['128','129'])).

thf('137',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('142',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('145',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('147',plain,(
    $false ),
    inference(demod,[status(thm)],['21','145','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYF6K1PJzl
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 209 iterations in 0.080s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(t76_mcart_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![E:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.53           ( ![F:$i]:
% 0.20/0.53             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.53               ( ![G:$i]:
% 0.20/0.53                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.53                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.53                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.53                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ![E:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.53              ( ![F:$i]:
% 0.20/0.53                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.53                  ( ![G:$i]:
% 0.20/0.53                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.53                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.53                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.53                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.20/0.53  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.53       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf(t10_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.53         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('9', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X9 : $i, X11 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf(t5_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.53          | ~ (v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t50_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ~( ![D:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.53                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.53                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.53                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (((X21) = (k1_xboole_0))
% 0.20/0.53          | ((X22) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.20/0.53          | ((X24) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.20/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)
% 0.20/0.53        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)
% 0.20/0.53        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('27', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (((X21) = (k1_xboole_0))
% 0.20/0.53          | ((X22) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.20/0.53          | ((X24) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '36'])).
% 0.20/0.53  thf('38', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.53  thf('39', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('41', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('46', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '46'])).
% 0.20/0.53  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.53  thf('49', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.53  thf(t69_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.53       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X7 @ X8)
% 0.20/0.53          | ~ (r1_tarski @ X7 @ X8)
% 0.20/0.53          | (v1_xboole_0 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '52'])).
% 0.20/0.53  thf('54', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('56', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['53', '56'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k2_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X18) @ X19)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k1_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['67', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '75'])).
% 0.20/0.53  thf('77', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('79', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '80'])).
% 0.20/0.53  thf('82', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('87', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X15 @ X16 @ X17)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16) @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      (![X9 : $i, X11 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X2)
% 0.20/0.53          | (m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.53          | ~ (v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X2)
% 0.20/0.53          | ~ (v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('condensation', [status(thm)], ['93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '94'])).
% 0.20/0.53  thf('96', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['87', '95'])).
% 0.20/0.53  thf('97', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '97'])).
% 0.20/0.53  thf('99', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('100', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.53         (((X21) = (k1_xboole_0))
% 0.20/0.53          | ((X22) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X21 @ X22 @ X24 @ X23)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X23)))
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.20/0.53          | ((X24) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.20/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['100', '105'])).
% 0.20/0.53  thf('107', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.53  thf('109', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.53  thf('111', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('112', plain,
% 0.20/0.53      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['110', '111'])).
% 0.20/0.53  thf('113', plain,
% 0.20/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.53  thf('115', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['114', '115'])).
% 0.20/0.53  thf('117', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.53          | ~ (v1_xboole_0 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['117', '118'])).
% 0.20/0.53  thf('120', plain,
% 0.20/0.53      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['116', '119'])).
% 0.20/0.53  thf('121', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['120', '121'])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.20/0.53      inference('sup-', [status(thm)], ['99', '122'])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.20/0.53       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.20/0.53       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('125', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['98', '123', '124'])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['26', '125'])).
% 0.20/0.53  thf('127', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.20/0.53        | ((sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '126'])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('129', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X18) @ X20)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k2_zfmisc_1 @ X19 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('130', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['128', '129'])).
% 0.20/0.53  thf('131', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['127', '130'])).
% 0.20/0.53  thf('132', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('133', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.53  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('135', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['133', '134'])).
% 0.20/0.53  thf('136', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['128', '129'])).
% 0.20/0.53  thf('137', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('138', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('139', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['137', '138'])).
% 0.20/0.53  thf('140', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['136', '139'])).
% 0.20/0.53  thf('141', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('142', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['140', '141'])).
% 0.20/0.53  thf('143', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['135', '142'])).
% 0.20/0.53  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('145', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['143', '144'])).
% 0.20/0.53  thf('146', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '51'])).
% 0.20/0.53  thf('147', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '145', '146'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
