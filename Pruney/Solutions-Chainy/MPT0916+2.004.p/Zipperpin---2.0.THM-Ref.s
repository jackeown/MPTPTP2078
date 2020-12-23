%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s9bz9Nl8px

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 840 expanded)
%              Number of leaves         :   43 ( 288 expanded)
%              Depth                    :   28
%              Number of atoms          : 1582 (8268 expanded)
%              Number of equality atoms :  103 ( 255 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k3_zfmisc_1 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('17',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k3_zfmisc_1 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('53',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['40','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_E = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['56','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('72',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_E = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_E = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('80',plain,
    ( ( ( sk_E = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('82',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('83',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X44 ) @ X45 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X24 @ X25 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('87',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('96',plain,(
    ! [X0: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('101',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k3_zfmisc_1 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_zfmisc_1 @ X0 @ X2 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','108'])).

thf('110',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_E = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['80','115'])).

thf('117',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('118',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X30 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('119',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_G ) @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( k3_zfmisc_1 @ X41 @ X42 @ X43 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('121',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X37 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_G ) ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('124',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('128',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('135',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['126','133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X47 @ X48 @ X50 @ X49 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X49 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k3_zfmisc_1 @ X47 @ X48 @ X50 ) )
      | ( X50 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('138',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['18'])).

thf('140',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('142',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('143',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['140','143'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('146',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('148',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['141','142'])).

thf('150',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('151',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('158',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('162',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('164',plain,(
    ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['135','162','163'])).

thf('165',plain,(
    ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G ) @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['19','164'])).

thf('166',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','165'])).

thf('167',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('168',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('170',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('172',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('174',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('176',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','54'])).

thf('178',plain,(
    $false ),
    inference(demod,[status(thm)],['14','176','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s9bz9Nl8px
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:57:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.96/2.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.96/2.16  % Solved by: fo/fo7.sh
% 1.96/2.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.96/2.16  % done 5254 iterations in 1.688s
% 1.96/2.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.96/2.16  % SZS output start Refutation
% 1.96/2.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.96/2.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.96/2.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.96/2.16  thf(sk_F_type, type, sk_F: $i).
% 1.96/2.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.96/2.16  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.96/2.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.96/2.16  thf(sk_B_type, type, sk_B: $i > $i).
% 1.96/2.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.96/2.16  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.96/2.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.96/2.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.96/2.16  thf(sk_G_type, type, sk_G: $i).
% 1.96/2.16  thf(sk_E_type, type, sk_E: $i).
% 1.96/2.16  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.96/2.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.96/2.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.96/2.16  thf(sk_D_type, type, sk_D: $i).
% 1.96/2.16  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.96/2.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.96/2.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.96/2.16  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.96/2.16  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.96/2.16  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.96/2.16  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.96/2.16  thf(sk_A_type, type, sk_A: $i).
% 1.96/2.16  thf(t76_mcart_1, conjecture,
% 1.96/2.16    (![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.16     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.96/2.16       ( ![E:$i]:
% 1.96/2.16         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.96/2.16           ( ![F:$i]:
% 1.96/2.16             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 1.96/2.16               ( ![G:$i]:
% 1.96/2.16                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.96/2.16                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.96/2.16                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 1.96/2.16                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 1.96/2.16                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 1.96/2.16  thf(zf_stmt_0, negated_conjecture,
% 1.96/2.16    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.96/2.16        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.96/2.16          ( ![E:$i]:
% 1.96/2.16            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.96/2.16              ( ![F:$i]:
% 1.96/2.16                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 1.96/2.16                  ( ![G:$i]:
% 1.96/2.16                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.96/2.16                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.96/2.16                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 1.96/2.16                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 1.96/2.16                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.96/2.16    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 1.96/2.16  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf(d3_zfmisc_1, axiom,
% 1.96/2.16    (![A:$i,B:$i,C:$i]:
% 1.96/2.16     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.96/2.16       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.96/2.16  thf('1', plain,
% 1.96/2.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ X41 @ X42 @ X43)
% 1.96/2.16           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42) @ X43))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.96/2.16  thf(t10_mcart_1, axiom,
% 1.96/2.16    (![A:$i,B:$i,C:$i]:
% 1.96/2.16     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.96/2.16       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.96/2.16         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.96/2.16  thf('2', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k1_mcart_1 @ X44) @ X45)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('3', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.96/2.16          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['1', '2'])).
% 1.96/2.16  thf('4', plain,
% 1.96/2.16      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.96/2.16      inference('sup-', [status(thm)], ['0', '3'])).
% 1.96/2.16  thf('5', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k1_mcart_1 @ X44) @ X45)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 1.96/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.96/2.16  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf(t3_subset, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.96/2.16  thf('8', plain,
% 1.96/2.16      (![X32 : $i, X33 : $i]:
% 1.96/2.16         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t3_subset])).
% 1.96/2.16  thf('9', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.96/2.16      inference('sup-', [status(thm)], ['7', '8'])).
% 1.96/2.16  thf(d3_tarski, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( r1_tarski @ A @ B ) <=>
% 1.96/2.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.96/2.16  thf('10', plain,
% 1.96/2.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ X4)
% 1.96/2.16          | (r2_hidden @ X3 @ X5)
% 1.96/2.16          | ~ (r1_tarski @ X4 @ X5))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.16  thf('11', plain,
% 1.96/2.16      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 1.96/2.16      inference('sup-', [status(thm)], ['9', '10'])).
% 1.96/2.16  thf('12', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_A)),
% 1.96/2.16      inference('sup-', [status(thm)], ['6', '11'])).
% 1.96/2.16  thf(d1_xboole_0, axiom,
% 1.96/2.16    (![A:$i]:
% 1.96/2.16     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.96/2.16  thf('13', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.96/2.16      inference('sup-', [status(thm)], ['12', '13'])).
% 1.96/2.16  thf('15', plain,
% 1.96/2.16      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf(t50_mcart_1, axiom,
% 1.96/2.16    (![A:$i,B:$i,C:$i]:
% 1.96/2.16     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.96/2.16          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.96/2.16          ( ~( ![D:$i]:
% 1.96/2.16               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.96/2.16                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.96/2.16                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.96/2.16                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.96/2.16                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.96/2.16                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.96/2.16  thf('16', plain,
% 1.96/2.16      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.96/2.16         (((X47) = (k1_xboole_0))
% 1.96/2.16          | ((X48) = (k1_xboole_0))
% 1.96/2.16          | ((k5_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 1.96/2.16              = (k1_mcart_1 @ (k1_mcart_1 @ X49)))
% 1.96/2.16          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 1.96/2.16          | ((X50) = (k1_xboole_0)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.96/2.16  thf('17', plain,
% 1.96/2.16      ((((sk_C_2) = (k1_xboole_0))
% 1.96/2.16        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 1.96/2.16            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['15', '16'])).
% 1.96/2.16  thf('18', plain,
% 1.96/2.16      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)
% 1.96/2.16        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)
% 1.96/2.16        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('19', plain,
% 1.96/2.16      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)))),
% 1.96/2.16      inference('split', [status(esa)], ['18'])).
% 1.96/2.16  thf('20', plain,
% 1.96/2.16      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('21', plain,
% 1.96/2.16      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.96/2.16         (((X47) = (k1_xboole_0))
% 1.96/2.16          | ((X48) = (k1_xboole_0))
% 1.96/2.16          | ((k7_mcart_1 @ X47 @ X48 @ X50 @ X49) = (k2_mcart_1 @ X49))
% 1.96/2.16          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 1.96/2.16          | ((X50) = (k1_xboole_0)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.96/2.16  thf('22', plain,
% 1.96/2.16      ((((sk_C_2) = (k1_xboole_0))
% 1.96/2.16        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) = (k2_mcart_1 @ sk_G))
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['20', '21'])).
% 1.96/2.16  thf('23', plain,
% 1.96/2.16      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('split', [status(esa)], ['18'])).
% 1.96/2.16  thf('24', plain,
% 1.96/2.16      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 1.96/2.16         | ((sk_A) = (k1_xboole_0))
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_C_2) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['22', '23'])).
% 1.96/2.16  thf('25', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('26', plain,
% 1.96/2.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ X41 @ X42 @ X43)
% 1.96/2.16           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42) @ X43))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.96/2.16  thf('27', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k2_mcart_1 @ X44) @ X46)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('28', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.96/2.16          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['26', '27'])).
% 1.96/2.16  thf('29', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.96/2.16      inference('sup-', [status(thm)], ['25', '28'])).
% 1.96/2.16  thf('30', plain,
% 1.96/2.16      (((((sk_A) = (k1_xboole_0))
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_C_2) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('demod', [status(thm)], ['24', '29'])).
% 1.96/2.16  thf('31', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.96/2.16      inference('sup-', [status(thm)], ['25', '28'])).
% 1.96/2.16  thf('32', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_2))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('33', plain,
% 1.96/2.16      (![X32 : $i, X33 : $i]:
% 1.96/2.16         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t3_subset])).
% 1.96/2.16  thf('34', plain, ((r1_tarski @ sk_F @ sk_C_2)),
% 1.96/2.16      inference('sup-', [status(thm)], ['32', '33'])).
% 1.96/2.16  thf('35', plain,
% 1.96/2.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ X4)
% 1.96/2.16          | (r2_hidden @ X3 @ X5)
% 1.96/2.16          | ~ (r1_tarski @ X4 @ X5))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.16  thf('36', plain,
% 1.96/2.16      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_2) | ~ (r2_hidden @ X0 @ sk_F))),
% 1.96/2.16      inference('sup-', [status(thm)], ['34', '35'])).
% 1.96/2.16  thf('37', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_C_2)),
% 1.96/2.16      inference('sup-', [status(thm)], ['31', '36'])).
% 1.96/2.16  thf('38', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('39', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.96/2.16      inference('sup-', [status(thm)], ['37', '38'])).
% 1.96/2.16  thf('40', plain,
% 1.96/2.16      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_A) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['30', '39'])).
% 1.96/2.16  thf(t48_xboole_1, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.96/2.16  thf('41', plain,
% 1.96/2.16      (![X17 : $i, X18 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.96/2.16           = (k3_xboole_0 @ X17 @ X18))),
% 1.96/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.96/2.16  thf('42', plain,
% 1.96/2.16      (![X17 : $i, X18 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.96/2.16           = (k3_xboole_0 @ X17 @ X18))),
% 1.96/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.96/2.16  thf('43', plain,
% 1.96/2.16      (![X17 : $i, X18 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.96/2.16           = (k3_xboole_0 @ X17 @ X18))),
% 1.96/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.96/2.16  thf(t79_xboole_1, axiom,
% 1.96/2.16    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.96/2.16  thf('44', plain,
% 1.96/2.16      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 1.96/2.16      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.96/2.16  thf('45', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 1.96/2.16      inference('sup+', [status(thm)], ['43', '44'])).
% 1.96/2.16  thf('46', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.96/2.16          (k3_xboole_0 @ X1 @ X0))),
% 1.96/2.16      inference('sup+', [status(thm)], ['42', '45'])).
% 1.96/2.16  thf('47', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.96/2.16          (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.96/2.16      inference('sup+', [status(thm)], ['41', '46'])).
% 1.96/2.16  thf('48', plain,
% 1.96/2.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.96/2.16  thf('49', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.96/2.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.96/2.16  thf('50', plain,
% 1.96/2.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ X4)
% 1.96/2.16          | (r2_hidden @ X3 @ X5)
% 1.96/2.16          | ~ (r1_tarski @ X4 @ X5))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.16  thf('51', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['49', '50'])).
% 1.96/2.16  thf('52', plain,
% 1.96/2.16      (![X0 : $i]:
% 1.96/2.16         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['48', '51'])).
% 1.96/2.16  thf(t4_xboole_0, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.96/2.16            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.96/2.16       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.96/2.16            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.96/2.16  thf('53', plain,
% 1.96/2.16      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.96/2.16          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.96/2.16      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.96/2.16  thf('54', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['52', '53'])).
% 1.96/2.16  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('56', plain,
% 1.96/2.16      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('demod', [status(thm)], ['40', '55'])).
% 1.96/2.16  thf('57', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('58', plain,
% 1.96/2.16      (![X32 : $i, X33 : $i]:
% 1.96/2.16         ((r1_tarski @ X32 @ X33) | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t3_subset])).
% 1.96/2.16  thf('59', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 1.96/2.16      inference('sup-', [status(thm)], ['57', '58'])).
% 1.96/2.16  thf('60', plain,
% 1.96/2.16      (![X4 : $i, X6 : $i]:
% 1.96/2.16         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.16  thf('61', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('62', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['60', '61'])).
% 1.96/2.16  thf('63', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.96/2.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.96/2.16  thf(d10_xboole_0, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.96/2.16  thf('64', plain,
% 1.96/2.16      (![X13 : $i, X15 : $i]:
% 1.96/2.16         (((X13) = (X15))
% 1.96/2.16          | ~ (r1_tarski @ X15 @ X13)
% 1.96/2.16          | ~ (r1_tarski @ X13 @ X15))),
% 1.96/2.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.96/2.16  thf('65', plain,
% 1.96/2.16      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['63', '64'])).
% 1.96/2.16  thf('66', plain,
% 1.96/2.16      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['62', '65'])).
% 1.96/2.16  thf('67', plain,
% 1.96/2.16      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['63', '64'])).
% 1.96/2.16  thf('68', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         (~ (r1_tarski @ X1 @ X0)
% 1.96/2.16          | ~ (v1_xboole_0 @ X0)
% 1.96/2.16          | ((X1) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['66', '67'])).
% 1.96/2.16  thf('69', plain, ((((sk_E) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.96/2.16      inference('sup-', [status(thm)], ['59', '68'])).
% 1.96/2.16  thf('70', plain,
% 1.96/2.16      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.96/2.16         | ((sk_A) = (k1_xboole_0))
% 1.96/2.16         | ((sk_E) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['56', '69'])).
% 1.96/2.16  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('72', plain,
% 1.96/2.16      (((((sk_A) = (k1_xboole_0)) | ((sk_E) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('demod', [status(thm)], ['70', '71'])).
% 1.96/2.16  thf('73', plain,
% 1.96/2.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('74', plain,
% 1.96/2.16      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 1.96/2.16      inference('sup-', [status(thm)], ['9', '10'])).
% 1.96/2.16  thf('75', plain,
% 1.96/2.16      (((v1_xboole_0 @ sk_D) | (r2_hidden @ (sk_B @ sk_D) @ sk_A))),
% 1.96/2.16      inference('sup-', [status(thm)], ['73', '74'])).
% 1.96/2.16  thf('76', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('77', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 1.96/2.16      inference('sup-', [status(thm)], ['75', '76'])).
% 1.96/2.16  thf('78', plain,
% 1.96/2.16      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.96/2.16         | ((sk_E) = (k1_xboole_0))
% 1.96/2.16         | (v1_xboole_0 @ sk_D)))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['72', '77'])).
% 1.96/2.16  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('80', plain,
% 1.96/2.16      (((((sk_E) = (k1_xboole_0)) | (v1_xboole_0 @ sk_D)))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('demod', [status(thm)], ['78', '79'])).
% 1.96/2.16  thf('81', plain,
% 1.96/2.16      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['62', '65'])).
% 1.96/2.16  thf('82', plain,
% 1.96/2.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('83', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k1_mcart_1 @ X44) @ X45)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('84', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.96/2.16          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.96/2.16      inference('sup-', [status(thm)], ['82', '83'])).
% 1.96/2.16  thf('85', plain,
% 1.96/2.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('86', plain,
% 1.96/2.16      (![X24 : $i, X25 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X24 @ X25) @ X25)),
% 1.96/2.16      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.96/2.16  thf(symmetry_r1_xboole_0, axiom,
% 1.96/2.16    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.96/2.16  thf('87', plain,
% 1.96/2.16      (![X7 : $i, X8 : $i]:
% 1.96/2.16         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.96/2.16      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.96/2.16  thf('88', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.16  thf(t83_xboole_1, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.96/2.16  thf('89', plain,
% 1.96/2.16      (![X26 : $i, X27 : $i]:
% 1.96/2.16         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 1.96/2.16      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.96/2.16  thf('90', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['88', '89'])).
% 1.96/2.16  thf('91', plain,
% 1.96/2.16      (![X17 : $i, X18 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.96/2.16           = (k3_xboole_0 @ X17 @ X18))),
% 1.96/2.16      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.96/2.16  thf('92', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((k4_xboole_0 @ X0 @ X0)
% 1.96/2.16           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.96/2.16      inference('sup+', [status(thm)], ['90', '91'])).
% 1.96/2.16  thf('93', plain,
% 1.96/2.16      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 1.96/2.16          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.96/2.16      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.96/2.16  thf('94', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 1.96/2.16          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['92', '93'])).
% 1.96/2.16  thf('95', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['86', '87'])).
% 1.96/2.16  thf('96', plain,
% 1.96/2.16      (![X0 : $i, X2 : $i]: ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))),
% 1.96/2.16      inference('demod', [status(thm)], ['94', '95'])).
% 1.96/2.16  thf('97', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['85', '96'])).
% 1.96/2.16  thf('98', plain,
% 1.96/2.16      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['62', '65'])).
% 1.96/2.16  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['97', '98'])).
% 1.96/2.16  thf('100', plain,
% 1.96/2.16      (![X0 : $i, X2 : $i]: ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))),
% 1.96/2.16      inference('demod', [status(thm)], ['94', '95'])).
% 1.96/2.16  thf('101', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['99', '100'])).
% 1.96/2.16  thf('102', plain,
% 1.96/2.16      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['84', '101'])).
% 1.96/2.16  thf('103', plain,
% 1.96/2.16      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['62', '65'])).
% 1.96/2.16  thf('104', plain,
% 1.96/2.16      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['102', '103'])).
% 1.96/2.16  thf('105', plain,
% 1.96/2.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ X41 @ X42 @ X43)
% 1.96/2.16           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42) @ X43))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.96/2.16  thf('106', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0)
% 1.96/2.16           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.96/2.16      inference('sup+', [status(thm)], ['104', '105'])).
% 1.96/2.16  thf('107', plain,
% 1.96/2.16      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['102', '103'])).
% 1.96/2.16  thf('108', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ k1_xboole_0 @ X1 @ X0) = (k1_xboole_0))),
% 1.96/2.16      inference('demod', [status(thm)], ['106', '107'])).
% 1.96/2.16  thf('109', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.96/2.16         (((k3_zfmisc_1 @ X0 @ X2 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.96/2.16      inference('sup+', [status(thm)], ['81', '108'])).
% 1.96/2.16  thf('110', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('111', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('112', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.96/2.16      inference('sup-', [status(thm)], ['110', '111'])).
% 1.96/2.16  thf('113', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_D))),
% 1.96/2.16      inference('sup-', [status(thm)], ['109', '112'])).
% 1.96/2.16  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('115', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.96/2.16      inference('demod', [status(thm)], ['113', '114'])).
% 1.96/2.16  thf('116', plain,
% 1.96/2.16      ((((sk_E) = (k1_xboole_0)))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['80', '115'])).
% 1.96/2.16  thf('117', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf(t63_subset_1, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( r2_hidden @ A @ B ) =>
% 1.96/2.16       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.96/2.16  thf('118', plain,
% 1.96/2.16      (![X30 : $i, X31 : $i]:
% 1.96/2.16         ((m1_subset_1 @ (k1_tarski @ X30) @ (k1_zfmisc_1 @ X31))
% 1.96/2.16          | ~ (r2_hidden @ X30 @ X31))),
% 1.96/2.16      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.96/2.16  thf('119', plain,
% 1.96/2.16      ((m1_subset_1 @ (k1_tarski @ sk_G) @ 
% 1.96/2.16        (k1_zfmisc_1 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['117', '118'])).
% 1.96/2.16  thf('120', plain,
% 1.96/2.16      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.96/2.16         ((k3_zfmisc_1 @ X41 @ X42 @ X43)
% 1.96/2.16           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42) @ X43))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.96/2.16  thf(cc3_relset_1, axiom,
% 1.96/2.16    (![A:$i,B:$i]:
% 1.96/2.16     ( ( v1_xboole_0 @ A ) =>
% 1.96/2.16       ( ![C:$i]:
% 1.96/2.16         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.96/2.16           ( v1_xboole_0 @ C ) ) ) ))).
% 1.96/2.16  thf('121', plain,
% 1.96/2.16      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.96/2.16         (~ (v1_xboole_0 @ X35)
% 1.96/2.16          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X37)))
% 1.96/2.16          | (v1_xboole_0 @ X36))),
% 1.96/2.16      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.96/2.16  thf('122', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.96/2.16         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)))
% 1.96/2.16          | (v1_xboole_0 @ X3)
% 1.96/2.16          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['120', '121'])).
% 1.96/2.16  thf('123', plain,
% 1.96/2.16      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))
% 1.96/2.16        | (v1_xboole_0 @ (k1_tarski @ sk_G)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['119', '122'])).
% 1.96/2.16  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.96/2.16  thf('124', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X29))),
% 1.96/2.16      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.96/2.16  thf('125', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.96/2.16      inference('clc', [status(thm)], ['123', '124'])).
% 1.96/2.16  thf('126', plain,
% 1.96/2.16      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ k1_xboole_0)))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['116', '125'])).
% 1.96/2.16  thf('127', plain,
% 1.96/2.16      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('128', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k2_mcart_1 @ X44) @ X46)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('129', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]:
% 1.96/2.16         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.96/2.16          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['127', '128'])).
% 1.96/2.16  thf('130', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['99', '100'])).
% 1.96/2.16  thf('131', plain,
% 1.96/2.16      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['129', '130'])).
% 1.96/2.16  thf('132', plain,
% 1.96/2.16      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['62', '65'])).
% 1.96/2.16  thf('133', plain,
% 1.96/2.16      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.96/2.16      inference('sup-', [status(thm)], ['131', '132'])).
% 1.96/2.16  thf('134', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('135', plain,
% 1.96/2.16      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 1.96/2.16      inference('demod', [status(thm)], ['126', '133', '134'])).
% 1.96/2.16  thf('136', plain,
% 1.96/2.16      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_2))),
% 1.96/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.96/2.16  thf('137', plain,
% 1.96/2.16      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.96/2.16         (((X47) = (k1_xboole_0))
% 1.96/2.16          | ((X48) = (k1_xboole_0))
% 1.96/2.16          | ((k6_mcart_1 @ X47 @ X48 @ X50 @ X49)
% 1.96/2.16              = (k2_mcart_1 @ (k1_mcart_1 @ X49)))
% 1.96/2.16          | ~ (m1_subset_1 @ X49 @ (k3_zfmisc_1 @ X47 @ X48 @ X50))
% 1.96/2.16          | ((X50) = (k1_xboole_0)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.96/2.16  thf('138', plain,
% 1.96/2.16      ((((sk_C_2) = (k1_xboole_0))
% 1.96/2.16        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G)
% 1.96/2.16            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['136', '137'])).
% 1.96/2.16  thf('139', plain,
% 1.96/2.16      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('split', [status(esa)], ['18'])).
% 1.96/2.16  thf('140', plain,
% 1.96/2.16      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 1.96/2.16         | ((sk_A) = (k1_xboole_0))
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_C_2) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['138', '139'])).
% 1.96/2.16  thf('141', plain,
% 1.96/2.16      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.96/2.16      inference('sup-', [status(thm)], ['0', '3'])).
% 1.96/2.16  thf('142', plain,
% 1.96/2.16      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.96/2.16         ((r2_hidden @ (k2_mcart_1 @ X44) @ X46)
% 1.96/2.16          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ X45 @ X46)))),
% 1.96/2.16      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.96/2.16  thf('143', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 1.96/2.16      inference('sup-', [status(thm)], ['141', '142'])).
% 1.96/2.16  thf('144', plain,
% 1.96/2.16      (((((sk_A) = (k1_xboole_0))
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_C_2) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('demod', [status(thm)], ['140', '143'])).
% 1.96/2.16  thf('145', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.96/2.16      inference('sup-', [status(thm)], ['37', '38'])).
% 1.96/2.16  thf('146', plain,
% 1.96/2.16      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.96/2.16         | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16         | ((sk_A) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['144', '145'])).
% 1.96/2.16  thf('147', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('148', plain,
% 1.96/2.16      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('demod', [status(thm)], ['146', '147'])).
% 1.96/2.16  thf('149', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 1.96/2.16      inference('sup-', [status(thm)], ['141', '142'])).
% 1.96/2.16  thf('150', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 1.96/2.16      inference('sup-', [status(thm)], ['57', '58'])).
% 1.96/2.16  thf('151', plain,
% 1.96/2.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.96/2.16         (~ (r2_hidden @ X3 @ X4)
% 1.96/2.16          | (r2_hidden @ X3 @ X5)
% 1.96/2.16          | ~ (r1_tarski @ X4 @ X5))),
% 1.96/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.96/2.16  thf('152', plain,
% 1.96/2.16      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 1.96/2.16      inference('sup-', [status(thm)], ['150', '151'])).
% 1.96/2.16  thf('153', plain,
% 1.96/2.16      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_B_1)),
% 1.96/2.16      inference('sup-', [status(thm)], ['149', '152'])).
% 1.96/2.16  thf('154', plain,
% 1.96/2.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.96/2.16      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.96/2.16  thf('155', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.96/2.16      inference('sup-', [status(thm)], ['153', '154'])).
% 1.96/2.16  thf('156', plain,
% 1.96/2.16      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['148', '155'])).
% 1.96/2.16  thf('157', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('158', plain,
% 1.96/2.16      ((((sk_A) = (k1_xboole_0)))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('demod', [status(thm)], ['156', '157'])).
% 1.96/2.16  thf('159', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.96/2.16      inference('sup-', [status(thm)], ['12', '13'])).
% 1.96/2.16  thf('160', plain,
% 1.96/2.16      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.96/2.16         <= (~
% 1.96/2.16             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['158', '159'])).
% 1.96/2.16  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('162', plain,
% 1.96/2.16      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E))),
% 1.96/2.16      inference('demod', [status(thm)], ['160', '161'])).
% 1.96/2.16  thf('163', plain,
% 1.96/2.16      (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)) | 
% 1.96/2.16       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_E)) | 
% 1.96/2.16       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_F))),
% 1.96/2.16      inference('split', [status(esa)], ['18'])).
% 1.96/2.16  thf('164', plain,
% 1.96/2.16      (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D))),
% 1.96/2.16      inference('sat_resolution*', [status(thm)], ['135', '162', '163'])).
% 1.96/2.16  thf('165', plain,
% 1.96/2.16      (~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_G) @ sk_D)),
% 1.96/2.16      inference('simpl_trail', [status(thm)], ['19', '164'])).
% 1.96/2.16  thf('166', plain,
% 1.96/2.16      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 1.96/2.16        | ((sk_A) = (k1_xboole_0))
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_C_2) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['17', '165'])).
% 1.96/2.16  thf('167', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 1.96/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.96/2.16  thf('168', plain,
% 1.96/2.16      ((((sk_A) = (k1_xboole_0))
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_C_2) = (k1_xboole_0)))),
% 1.96/2.16      inference('demod', [status(thm)], ['166', '167'])).
% 1.96/2.16  thf('169', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.96/2.16      inference('sup-', [status(thm)], ['37', '38'])).
% 1.96/2.16  thf('170', plain,
% 1.96/2.16      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.96/2.16        | ((sk_B_1) = (k1_xboole_0))
% 1.96/2.16        | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['168', '169'])).
% 1.96/2.16  thf('171', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('172', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('demod', [status(thm)], ['170', '171'])).
% 1.96/2.16  thf('173', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.96/2.16      inference('sup-', [status(thm)], ['153', '154'])).
% 1.96/2.16  thf('174', plain,
% 1.96/2.16      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 1.96/2.16      inference('sup-', [status(thm)], ['172', '173'])).
% 1.96/2.16  thf('175', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('176', plain, (((sk_A) = (k1_xboole_0))),
% 1.96/2.16      inference('demod', [status(thm)], ['174', '175'])).
% 1.96/2.16  thf('177', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.96/2.16      inference('sup-', [status(thm)], ['47', '54'])).
% 1.96/2.16  thf('178', plain, ($false),
% 1.96/2.16      inference('demod', [status(thm)], ['14', '176', '177'])).
% 1.96/2.16  
% 1.96/2.16  % SZS output end Refutation
% 1.96/2.16  
% 1.96/2.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
