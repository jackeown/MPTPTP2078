%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O2NibY8qWw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 633 expanded)
%              Number of leaves         :   35 ( 217 expanded)
%              Depth                    :   24
%              Number of atoms          : 1327 (6690 expanded)
%              Number of equality atoms :   85 ( 126 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_A ),
    inference('sup-',[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('17',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k2_mcart_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('22',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['25','28'])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_F @ sk_C_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

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

thf('47',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_E = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('68',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('76',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_zfmisc_1 @ X23 @ X24 @ X25 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('88',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('89',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ ( k1_mcart_1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['82','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','95'])).

thf('97',plain,
    ( ( sk_E = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['76','96'])).

thf('98',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('99',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('100',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['97','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('105',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X29 @ X30 @ X32 @ X31 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k3_zfmisc_1 @ X29 @ X30 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('108',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('110',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('112',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('114',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('116',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('118',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('119',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('126',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('130',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('132',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['105','130','131'])).

thf('133',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['19','132'])).

thf('134',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','133'])).

thf('135',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['98','99'])).

thf('136',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('138',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('140',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('144',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['14','144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O2NibY8qWw
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:28:15 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 713 iterations in 0.329s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.80  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.61/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.80  thf(sk_G_type, type, sk_G: $i).
% 0.61/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.80  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.61/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.80  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.61/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.80  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.61/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.61/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.80  thf(sk_F_type, type, sk_F: $i).
% 0.61/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.61/0.80  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.61/0.80  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.61/0.80  thf(t76_mcart_1, conjecture,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.80       ( ![E:$i]:
% 0.61/0.80         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.61/0.80           ( ![F:$i]:
% 0.61/0.80             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.61/0.80               ( ![G:$i]:
% 0.61/0.80                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.61/0.80                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.61/0.80                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.61/0.80                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.61/0.80                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.61/0.80          ( ![E:$i]:
% 0.61/0.80            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.61/0.80              ( ![F:$i]:
% 0.61/0.80                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.61/0.80                  ( ![G:$i]:
% 0.61/0.80                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.61/0.80                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.61/0.80                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.61/0.80                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.61/0.80                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.61/0.80  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(d3_zfmisc_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.61/0.80       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.61/0.80  thf('1', plain,
% 0.61/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.80         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.61/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.61/0.80  thf(t10_mcart_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.61/0.80       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.61/0.80         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('3', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.61/0.80          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.61/0.80      inference('sup-', [status(thm)], ['0', '3'])).
% 0.61/0.80  thf('5', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.61/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.80  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t3_subset, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.80  thf('8', plain,
% 0.61/0.80      (![X20 : $i, X21 : $i]:
% 0.61/0.80         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.80  thf('9', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.61/0.80  thf(d3_tarski, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.80          | (r2_hidden @ X3 @ X5)
% 0.61/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.80  thf('11', plain,
% 0.61/0.80      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.61/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['6', '11'])).
% 0.61/0.80  thf(d1_xboole_0, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.80  thf('13', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('15', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf(t50_mcart_1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.61/0.80          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.61/0.80          ( ~( ![D:$i]:
% 0.61/0.80               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.61/0.80                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.61/0.80                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.61/0.80                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.61/0.80                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.61/0.80                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.61/0.80  thf('16', plain,
% 0.61/0.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.80         (((X29) = (k1_xboole_0))
% 0.61/0.80          | ((X30) = (k1_xboole_0))
% 0.61/0.80          | ((k6_mcart_1 @ X29 @ X30 @ X32 @ X31)
% 0.61/0.80              = (k2_mcart_1 @ (k1_mcart_1 @ X31)))
% 0.61/0.80          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 0.61/0.80          | ((X32) = (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.61/0.80  thf('17', plain,
% 0.61/0.80      ((((sk_C_2) = (k1_xboole_0))
% 0.61/0.80        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 0.61/0.80            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)
% 0.61/0.80        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)
% 0.61/0.80        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 0.61/0.80      inference('split', [status(esa)], ['18'])).
% 0.61/0.80  thf('20', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('21', plain,
% 0.61/0.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.80         (((X29) = (k1_xboole_0))
% 0.61/0.80          | ((X30) = (k1_xboole_0))
% 0.61/0.80          | ((k7_mcart_1 @ X29 @ X30 @ X32 @ X31) = (k2_mcart_1 @ X31))
% 0.61/0.80          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 0.61/0.80          | ((X32) = (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.61/0.80  thf('22', plain,
% 0.61/0.80      ((((sk_C_2) = (k1_xboole_0))
% 0.61/0.80        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.80  thf('23', plain,
% 0.61/0.80      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('split', [status(esa)], ['18'])).
% 0.61/0.80  thf('24', plain,
% 0.61/0.80      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.61/0.80         | ((sk_A) = (k1_xboole_0))
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_C_2) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.61/0.80  thf('25', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.80         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.61/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k2_mcart_1 @ X26) @ X28)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('28', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.61/0.80          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.61/0.80  thf('29', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.61/0.80      inference('sup-', [status(thm)], ['25', '28'])).
% 0.61/0.80  thf('30', plain,
% 0.61/0.80      (((((sk_A) = (k1_xboole_0))
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_C_2) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('demod', [status(thm)], ['24', '29'])).
% 0.61/0.80  thf('31', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.61/0.80      inference('sup-', [status(thm)], ['25', '28'])).
% 0.61/0.80  thf('32', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_2))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('33', plain,
% 0.61/0.80      (![X20 : $i, X21 : $i]:
% 0.61/0.80         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.80  thf('34', plain, ((r1_tarski @ sk_F @ sk_C_2)),
% 0.61/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.61/0.80  thf('35', plain,
% 0.61/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.80          | (r2_hidden @ X3 @ X5)
% 0.61/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.80  thf('36', plain,
% 0.61/0.80      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.61/0.80      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.80  thf('37', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_2)),
% 0.61/0.80      inference('sup-', [status(thm)], ['31', '36'])).
% 0.61/0.80  thf('38', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('39', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.61/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('40', plain,
% 0.61/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_A) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['30', '39'])).
% 0.61/0.80  thf(t79_xboole_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.61/0.80  thf('41', plain,
% 0.61/0.80      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.61/0.80      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.61/0.80  thf('42', plain,
% 0.61/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.61/0.80  thf('43', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.61/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.80  thf('44', plain,
% 0.61/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.80          | (r2_hidden @ X3 @ X5)
% 0.61/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.80  thf('45', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.80  thf('46', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['42', '45'])).
% 0.61/0.80  thf(t3_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.61/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.61/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.61/0.80  thf('47', plain,
% 0.61/0.80      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X9 @ X7)
% 0.61/0.80          | ~ (r2_hidden @ X9 @ X10)
% 0.61/0.80          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('48', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.61/0.80          | ~ (r2_hidden @ (sk_B @ k1_xboole_0) @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.80  thf('49', plain,
% 0.61/0.80      (![X0 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['42', '45'])).
% 0.61/0.80  thf('50', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_xboole_0 @ X0 @ X1) | (v1_xboole_0 @ k1_xboole_0))),
% 0.61/0.80      inference('clc', [status(thm)], ['48', '49'])).
% 0.61/0.80  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('52', plain,
% 0.61/0.80      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('demod', [status(thm)], ['40', '51'])).
% 0.61/0.80  thf('53', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('54', plain,
% 0.61/0.80      (![X20 : $i, X21 : $i]:
% 0.61/0.80         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.80  thf('55', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.61/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.80  thf('56', plain,
% 0.61/0.80      (![X4 : $i, X6 : $i]:
% 0.61/0.80         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.80  thf('57', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('58', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['56', '57'])).
% 0.61/0.80  thf('59', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.61/0.80      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.80  thf(d10_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.80  thf('60', plain,
% 0.61/0.80      (![X11 : $i, X13 : $i]:
% 0.61/0.80         (((X11) = (X13))
% 0.61/0.80          | ~ (r1_tarski @ X13 @ X11)
% 0.61/0.80          | ~ (r1_tarski @ X11 @ X13))),
% 0.61/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.80  thf('61', plain,
% 0.61/0.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.80  thf('62', plain,
% 0.61/0.80      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['58', '61'])).
% 0.61/0.80  thf('63', plain,
% 0.61/0.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['59', '60'])).
% 0.61/0.80  thf('64', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.61/0.80          | ~ (v1_xboole_0 @ X0)
% 0.61/0.80          | ((X1) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['62', '63'])).
% 0.61/0.80  thf('65', plain, ((((sk_E) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['55', '64'])).
% 0.61/0.80  thf('66', plain,
% 0.61/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80         | ((sk_A) = (k1_xboole_0))
% 0.61/0.80         | ((sk_E) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['52', '65'])).
% 0.61/0.80  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('68', plain,
% 0.61/0.80      (((((sk_A) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('demod', [status(thm)], ['66', '67'])).
% 0.61/0.80  thf('69', plain,
% 0.61/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('70', plain,
% 0.61/0.80      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.61/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf('71', plain,
% 0.61/0.80      (((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_B @ sk_D) @ sk_A))),
% 0.61/0.80      inference('sup-', [status(thm)], ['69', '70'])).
% 0.61/0.80  thf('72', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('73', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.61/0.80      inference('sup-', [status(thm)], ['71', '72'])).
% 0.61/0.80  thf('74', plain,
% 0.61/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80         | ((sk_E) = (k1_xboole_0))
% 0.61/0.80         | (v1_xboole_0 @ sk_D)))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['68', '73'])).
% 0.61/0.80  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('76', plain,
% 0.61/0.80      (((((sk_E) = (k1_xboole_0)) | (v1_xboole_0 @ sk_D)))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('demod', [status(thm)], ['74', '75'])).
% 0.61/0.80  thf('77', plain,
% 0.61/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('78', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('79', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.61/0.80          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['77', '78'])).
% 0.61/0.80  thf('80', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('81', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.61/0.80  thf('82', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('83', plain,
% 0.61/0.80      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.80         ((k3_zfmisc_1 @ X23 @ X24 @ X25)
% 0.61/0.80           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24) @ X25))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.61/0.80  thf('84', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.61/0.80  thf('85', plain,
% 0.61/0.80      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['58', '61'])).
% 0.61/0.80  thf('86', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['84', '85'])).
% 0.61/0.80  thf('87', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['84', '85'])).
% 0.61/0.80  thf('88', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k1_mcart_1 @ X26) @ X27)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('89', plain,
% 0.61/0.80      (![X1 : $i, X2 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.61/0.80          | ~ (v1_xboole_0 @ X1)
% 0.61/0.80          | (r2_hidden @ (k1_mcart_1 @ X2) @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['87', '88'])).
% 0.61/0.80  thf('90', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('91', plain,
% 0.61/0.80      (![X1 : $i, X2 : $i]:
% 0.61/0.80         (~ (v1_xboole_0 @ X1) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 0.61/0.80      inference('clc', [status(thm)], ['89', '90'])).
% 0.61/0.80  thf('92', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.61/0.80          | ~ (v1_xboole_0 @ X1)
% 0.61/0.80          | ~ (v1_xboole_0 @ X3))),
% 0.61/0.80      inference('sup-', [status(thm)], ['86', '91'])).
% 0.61/0.80  thf('93', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('condensation', [status(thm)], ['92'])).
% 0.61/0.80  thf('94', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.61/0.80          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['83', '93'])).
% 0.61/0.80  thf('95', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.61/0.80      inference('sup-', [status(thm)], ['82', '94'])).
% 0.61/0.80  thf('96', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.61/0.80      inference('sup-', [status(thm)], ['81', '95'])).
% 0.61/0.80  thf('97', plain,
% 0.61/0.80      ((((sk_E) = (k1_xboole_0)))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['76', '96'])).
% 0.61/0.80  thf('98', plain,
% 0.61/0.80      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.61/0.80      inference('sup-', [status(thm)], ['0', '3'])).
% 0.61/0.80  thf('99', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.80         ((r2_hidden @ (k2_mcart_1 @ X26) @ X28)
% 0.61/0.80          | ~ (r2_hidden @ X26 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.61/0.80  thf('100', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.61/0.80      inference('sup-', [status(thm)], ['98', '99'])).
% 0.61/0.80  thf('101', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('102', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.61/0.80      inference('sup-', [status(thm)], ['100', '101'])).
% 0.61/0.80  thf('103', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['97', '102'])).
% 0.61/0.80  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('105', plain,
% 0.61/0.80      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.61/0.80      inference('demod', [status(thm)], ['103', '104'])).
% 0.61/0.80  thf('106', plain,
% 0.61/0.80      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('107', plain,
% 0.61/0.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.80         (((X29) = (k1_xboole_0))
% 0.61/0.80          | ((X30) = (k1_xboole_0))
% 0.61/0.80          | ((k5_mcart_1 @ X29 @ X30 @ X32 @ X31)
% 0.61/0.80              = (k1_mcart_1 @ (k1_mcart_1 @ X31)))
% 0.61/0.80          | ~ (m1_subset_1 @ X31 @ (k3_zfmisc_1 @ X29 @ X30 @ X32))
% 0.61/0.80          | ((X32) = (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.61/0.80  thf('108', plain,
% 0.61/0.80      ((((sk_C_2) = (k1_xboole_0))
% 0.61/0.80        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 0.61/0.80            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['106', '107'])).
% 0.61/0.80  thf('109', plain,
% 0.61/0.80      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('split', [status(esa)], ['18'])).
% 0.61/0.80  thf('110', plain,
% 0.61/0.80      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.61/0.80         | ((sk_A) = (k1_xboole_0))
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_C_2) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['108', '109'])).
% 0.61/0.80  thf('111', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.61/0.80      inference('sup-', [status(thm)], ['4', '5'])).
% 0.61/0.80  thf('112', plain,
% 0.61/0.80      (((((sk_A) = (k1_xboole_0))
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_C_2) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('demod', [status(thm)], ['110', '111'])).
% 0.61/0.80  thf('113', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.61/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('114', plain,
% 0.61/0.80      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80         | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80         | ((sk_A) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['112', '113'])).
% 0.61/0.80  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('116', plain,
% 0.61/0.80      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('demod', [status(thm)], ['114', '115'])).
% 0.61/0.80  thf('117', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.61/0.80      inference('sup-', [status(thm)], ['98', '99'])).
% 0.61/0.80  thf('118', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.61/0.80      inference('sup-', [status(thm)], ['53', '54'])).
% 0.61/0.80  thf('119', plain,
% 0.61/0.80      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.80          | (r2_hidden @ X3 @ X5)
% 0.61/0.80          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.80      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.80  thf('120', plain,
% 0.61/0.80      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.61/0.80      inference('sup-', [status(thm)], ['118', '119'])).
% 0.61/0.80  thf('121', plain,
% 0.61/0.80      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B_1)),
% 0.61/0.80      inference('sup-', [status(thm)], ['117', '120'])).
% 0.61/0.80  thf('122', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.80  thf('123', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.61/0.80      inference('sup-', [status(thm)], ['121', '122'])).
% 0.61/0.80  thf('124', plain,
% 0.61/0.80      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['116', '123'])).
% 0.61/0.80  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('126', plain,
% 0.61/0.80      ((((sk_A) = (k1_xboole_0)))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('demod', [status(thm)], ['124', '125'])).
% 0.61/0.80  thf('127', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.61/0.80      inference('sup-', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf('128', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.61/0.80         <= (~
% 0.61/0.80             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['126', '127'])).
% 0.61/0.80  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('130', plain,
% 0.61/0.80      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))),
% 0.61/0.80      inference('demod', [status(thm)], ['128', '129'])).
% 0.61/0.80  thf('131', plain,
% 0.61/0.80      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)) | 
% 0.61/0.80       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)) | 
% 0.61/0.80       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 0.61/0.80      inference('split', [status(esa)], ['18'])).
% 0.61/0.80  thf('132', plain,
% 0.61/0.80      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))),
% 0.61/0.80      inference('sat_resolution*', [status(thm)], ['105', '130', '131'])).
% 0.61/0.80  thf('133', plain,
% 0.61/0.80      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)),
% 0.61/0.80      inference('simpl_trail', [status(thm)], ['19', '132'])).
% 0.61/0.80  thf('134', plain,
% 0.61/0.80      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.61/0.80        | ((sk_A) = (k1_xboole_0))
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_C_2) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '133'])).
% 0.61/0.80  thf('135', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.61/0.80      inference('sup-', [status(thm)], ['98', '99'])).
% 0.61/0.80  thf('136', plain,
% 0.61/0.80      ((((sk_A) = (k1_xboole_0))
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_C_2) = (k1_xboole_0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['134', '135'])).
% 0.61/0.80  thf('137', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.61/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('138', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.61/0.80        | ((sk_B_1) = (k1_xboole_0))
% 0.61/0.80        | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['136', '137'])).
% 0.61/0.80  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('140', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['138', '139'])).
% 0.61/0.80  thf('141', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.61/0.80      inference('sup-', [status(thm)], ['121', '122'])).
% 0.61/0.80  thf('142', plain,
% 0.61/0.80      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['140', '141'])).
% 0.61/0.80  thf('143', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('144', plain, (((sk_A) = (k1_xboole_0))),
% 0.61/0.80      inference('demod', [status(thm)], ['142', '143'])).
% 0.61/0.80  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['41', '50'])).
% 0.61/0.80  thf('146', plain, ($false),
% 0.61/0.80      inference('demod', [status(thm)], ['14', '144', '145'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.61/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
