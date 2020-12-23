%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KJxHoTixrH

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 577 expanded)
%              Number of leaves         :   31 ( 187 expanded)
%              Depth                    :   25
%              Number of atoms          : 1287 (6547 expanded)
%              Number of equality atoms :   73 ( 105 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k2_mcart_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('37',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['30','33'])).

thf('42',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['50','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_E ) @ X1 )
        | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['29','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_E ) ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_zfmisc_1 @ X17 @ X18 @ X19 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('69',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['66','80'])).

thf('82',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['54'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','79'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X23 @ X24 @ X26 @ X25 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X23 @ X24 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('94',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('96',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('98',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('100',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('102',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('104',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X20 ) @ X22 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('105',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B ),
    inference('sup-',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['102','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('116',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('118',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('120',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['25'])).

thf('122',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['91','120','121'])).

thf('123',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['26','122'])).

thf('124',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','123'])).

thf('125',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['103','104'])).

thf('126',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('130',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('132',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('134',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','55'])).

thf('136',plain,(
    $false ),
    inference(demod,[status(thm)],['21','134','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KJxHoTixrH
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:24:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 196 iterations in 0.077s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
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
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf(t10_mcart_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.53         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
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
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
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
% 0.20/0.53      (![X11 : $i, X13 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf(t5_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.53          | ~ (v1_xboole_0 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
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
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((X23) = (k1_xboole_0))
% 0.20/0.53          | ((X24) = (k1_xboole_0))
% 0.20/0.53          | ((k6_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.20/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.20/0.53          | ((X26) = (k1_xboole_0)))),
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
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k2_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((X23) = (k1_xboole_0))
% 0.20/0.53          | ((X24) = (k1_xboole_0))
% 0.20/0.53          | ((k7_mcart_1 @ X23 @ X24 @ X26 @ X25) = (k2_mcart_1 @ X25))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.20/0.53          | ((X26) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.53  thf('41', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.53  thf('42', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('44', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('49', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '49'])).
% 0.20/0.53  thf('51', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.53  thf('52', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.53  thf(t68_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.53       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.53          | (v1_xboole_0 @ X10)
% 0.20/0.53          | ~ (r1_tarski @ X10 @ X8)
% 0.20/0.53          | ~ (r1_tarski @ X10 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X0)
% 0.20/0.53          | (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('condensation', [status(thm)], ['54'])).
% 0.20/0.53  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['50', '56'])).
% 0.20/0.53  thf('58', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.53          | ~ (v1_xboole_0 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53           | ((sk_A) = (k1_xboole_0))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '60'])).
% 0.20/0.53  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((![X0 : $i, X1 : $i]:
% 0.20/0.53          ((r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_E) @ X1)
% 0.20/0.53           | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('condensation', [status(thm)], ['54'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_E))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((k3_zfmisc_1 @ X17 @ X18 @ X19)
% 0.20/0.53           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_mcart_1 @ X20) @ X21)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k1_mcart_1 @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      (![X11 : $i, X13 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X2)
% 0.20/0.53          | (m1_subset_1 @ (k2_zfmisc_1 @ X2 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X14 @ X15)
% 0.20/0.53          | ~ (v1_xboole_0 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X2)
% 0.20/0.53          | ~ (v1_xboole_0 @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.53      inference('condensation', [status(thm)], ['77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.53          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['68', '78'])).
% 0.20/0.53  thf('80', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '79'])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '80'])).
% 0.20/0.53  thf('82', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('condensation', [status(thm)], ['54'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r1_tarski @ (k2_zfmisc_1 @ X0 @ X1) @ X2) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.20/0.53      inference('condensation', [status(thm)], ['54'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('89', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '79'])).
% 0.20/0.53  thf('90', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.53         (((X23) = (k1_xboole_0))
% 0.20/0.53          | ((X24) = (k1_xboole_0))
% 0.20/0.53          | ((k5_mcart_1 @ X23 @ X24 @ X26 @ X25)
% 0.20/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X25)))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X23 @ X24 @ X26))
% 0.20/0.53          | ((X26) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      ((((sk_C_1) = (k1_xboole_0))
% 0.20/0.53        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.20/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.53  thf('97', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (((((sk_A) = (k1_xboole_0))
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_C_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.53  thf('99', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53         | ((sk_B) = (k1_xboole_0))
% 0.20/0.53         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.53  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['100', '101'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         ((r2_hidden @ (k2_mcart_1 @ X20) @ X22)
% 0.20/0.53          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X21 @ X22)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.53  thf('105', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('108', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.20/0.53      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.53  thf('111', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['105', '110'])).
% 0.20/0.53  thf('112', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('113', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['102', '113'])).
% 0.20/0.53  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.53  thf('117', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '20'])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.53  thf('119', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('120', plain,
% 0.20/0.53      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.20/0.53      inference('demod', [status(thm)], ['118', '119'])).
% 0.20/0.53  thf('121', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.20/0.53       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.20/0.53       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.20/0.53      inference('split', [status(esa)], ['25'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['91', '120', '121'])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['26', '122'])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.20/0.53        | ((sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '123'])).
% 0.20/0.53  thf('125', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      ((((sk_A) = (k1_xboole_0))
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['124', '125'])).
% 0.20/0.53  thf('127', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('128', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.53        | ((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['126', '127'])).
% 0.20/0.53  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('130', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['128', '129'])).
% 0.20/0.53  thf('131', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.53  thf('132', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['130', '131'])).
% 0.20/0.53  thf('133', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('134', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['132', '133'])).
% 0.20/0.53  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '55'])).
% 0.20/0.53  thf('136', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '134', '135'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
