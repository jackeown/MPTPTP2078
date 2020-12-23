%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hj7LlDkwl6

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:47 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 431 expanded)
%              Number of leaves         :   19 ( 135 expanded)
%              Depth                    :   27
%              Number of atoms          : 1377 (4339 expanded)
%              Number of equality atoms :  148 ( 492 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t126_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t121_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ ( k2_zfmisc_1 @ B @ C ) ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X19 @ X22 ) @ ( k2_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X19 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) @ ( k2_zfmisc_1 @ X22 @ X20 ) ) @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t121_zfmisc_1])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ ( k2_xboole_0 @ X15 @ X17 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X15 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X19 @ X22 ) @ ( k2_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) @ ( k2_zfmisc_1 @ X22 @ X20 ) ) @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X5 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X4 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ) @ ( k2_zfmisc_1 @ X4 @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X5 @ X4 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X5 @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X4 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) ) ) @ ( k2_zfmisc_1 @ X4 @ ( k2_zfmisc_1 @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X3 @ X1 ) @ X2 ) @ ( k4_xboole_0 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k4_xboole_0 @ sk_A @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['27'])).

thf('44',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['28','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X16 ) @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('54',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('55',plain,
    ( k1_xboole_0
    = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('57',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ ( k2_xboole_0 @ X15 @ X17 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X15 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X0 @ X2 )
      = ( k2_zfmisc_1 @ X0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ X1 )
      = ( k2_zfmisc_1 @ X2 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('66',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ ( k2_xboole_0 @ X15 @ X17 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X15 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X3 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X3 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','14','15','46','48','49','55','93'])).

thf('95',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('97',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X23 @ X25 ) @ ( k2_zfmisc_1 @ X24 @ X26 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 ) @ ( k2_zfmisc_1 @ X23 @ ( k4_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t126_zfmisc_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X1 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('106',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( k2_zfmisc_1 @ X18 @ ( k2_xboole_0 @ X15 @ X17 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X18 @ X15 ) @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
       != k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 )
       != k1_xboole_0 )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','112'])).

thf('114',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','89','92'])).

thf('115',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_D ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X10 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('118',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('121',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['28','44'])).

thf('124',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('126',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','124','125'])).

thf('127',plain,(
    $false ),
    inference(simplify,[status(thm)],['126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hj7LlDkwl6
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1122 iterations in 0.807s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(sk_D_type, type, sk_D: $i).
% 1.06/1.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.25  thf(t138_zfmisc_1, conjecture,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.06/1.25       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.25         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 1.06/1.25          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 1.06/1.25            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 1.06/1.25  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('1', plain,
% 1.06/1.25      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(l32_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.25  thf('2', plain,
% 1.06/1.25      (![X0 : $i, X2 : $i]:
% 1.06/1.25         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf(t126_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =
% 1.06/1.25       ( k2_xboole_0 @
% 1.06/1.25         ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ C ) @ B ) @ 
% 1.06/1.25         ( k2_zfmisc_1 @ A @ ( k4_xboole_0 @ B @ D ) ) ) ))).
% 1.06/1.25  thf('4', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf(t121_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.06/1.25     ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ C @ D ) ) =
% 1.06/1.25       ( k2_xboole_0 @
% 1.06/1.25         ( k2_xboole_0 @
% 1.06/1.25           ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ A @ D ) ) @ 
% 1.06/1.25           ( k2_zfmisc_1 @ B @ C ) ) @ 
% 1.06/1.25         ( k2_zfmisc_1 @ B @ D ) ) ))).
% 1.06/1.25  thf('5', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X19 @ X22) @ (k2_xboole_0 @ X20 @ X21))
% 1.06/1.25           = (k2_xboole_0 @ 
% 1.06/1.25              (k2_xboole_0 @ 
% 1.06/1.25               (k2_xboole_0 @ (k2_zfmisc_1 @ X19 @ X20) @ 
% 1.06/1.25                (k2_zfmisc_1 @ X19 @ X21)) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X22 @ X20)) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X22 @ X21)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t121_zfmisc_1])).
% 1.06/1.25  thf(t120_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.06/1.25         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.06/1.25       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.06/1.25         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X18 @ (k2_xboole_0 @ X15 @ X17))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X15) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X18 @ X17)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.06/1.25  thf('7', plain,
% 1.06/1.25      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X19 @ X22) @ (k2_xboole_0 @ X20 @ X21))
% 1.06/1.25           = (k2_xboole_0 @ 
% 1.06/1.25              (k2_xboole_0 @ (k2_zfmisc_1 @ X19 @ (k2_xboole_0 @ X20 @ X21)) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X22 @ X20)) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X22 @ X21)))),
% 1.06/1.25      inference('demod', [status(thm)], ['5', '6'])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X5 @ X4) @ 
% 1.06/1.25           (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 1.06/1.25            (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0))))
% 1.06/1.25           = (k2_xboole_0 @ 
% 1.06/1.25              (k2_xboole_0 @ 
% 1.06/1.25               (k2_zfmisc_1 @ X5 @ 
% 1.06/1.25                (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ 
% 1.06/1.25                 (k2_zfmisc_1 @ X1 @ X0))) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X4 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2))) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X4 @ (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['4', '7'])).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X5 @ X4) @ 
% 1.06/1.25           (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.06/1.25           = (k2_xboole_0 @ 
% 1.06/1.25              (k2_xboole_0 @ 
% 1.06/1.25               (k2_zfmisc_1 @ X5 @ 
% 1.06/1.25                (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ 
% 1.06/1.25                 (k2_zfmisc_1 @ X1 @ X0))) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X4 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2))) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X4 @ (k2_zfmisc_1 @ X3 @ (k4_xboole_0 @ X2 @ X0)))))),
% 1.06/1.25      inference('demod', [status(thm)], ['8', '9'])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.06/1.25           (k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25            (k2_zfmisc_1 @ sk_C @ sk_D)))
% 1.06/1.25           = (k2_xboole_0 @ 
% 1.06/1.25              (k2_xboole_0 @ (k2_zfmisc_1 @ X1 @ k1_xboole_0) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X0 @ 
% 1.06/1.25                (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B))) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X0 @ 
% 1.06/1.25               (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['3', '10'])).
% 1.06/1.25  thf('12', plain,
% 1.06/1.25      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf(t113_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.06/1.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.06/1.25  thf('13', plain,
% 1.06/1.25      (![X10 : $i, X11 : $i]:
% 1.06/1.25         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 1.06/1.25          | ((X11) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.25  thf('14', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('15', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf(t46_xboole_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.06/1.25  thf('19', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X3 @ X1) @ X2) @ 
% 1.06/1.25           (k4_xboole_0 @ (k2_zfmisc_1 @ X3 @ X2) @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.06/1.25           = (k1_xboole_0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.25  thf('20', plain,
% 1.06/1.25      (((k4_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) @ 
% 1.06/1.25         k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['16', '19'])).
% 1.06/1.25  thf(t3_boole, axiom,
% 1.06/1.25    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.25  thf('21', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('22', plain,
% 1.06/1.25      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 1.06/1.25      inference('demod', [status(thm)], ['20', '21'])).
% 1.06/1.25  thf(t117_zfmisc_1, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.06/1.25          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 1.06/1.25            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 1.06/1.25          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.06/1.25         (((X12) = (k1_xboole_0))
% 1.06/1.25          | (r1_tarski @ X13 @ X14)
% 1.06/1.25          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X12 @ X14)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.06/1.25  thf('24', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r1_tarski @ k1_xboole_0 @ 
% 1.06/1.25             (k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ X0))
% 1.06/1.25          | (r1_tarski @ sk_B @ X0)
% 1.06/1.25          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['22', '23'])).
% 1.06/1.25  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.06/1.25  thf('25', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.06/1.25      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((r1_tarski @ sk_B @ X0)
% 1.06/1.25          | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.06/1.25      inference('demod', [status(thm)], ['24', '25'])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 1.06/1.25      inference('split', [status(esa)], ['27'])).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      (((k2_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 1.06/1.25      inference('demod', [status(thm)], ['20', '21'])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         (((X9) = (k1_xboole_0))
% 1.06/1.25          | ((X10) = (k1_xboole_0))
% 1.06/1.25          | ((k2_zfmisc_1 @ X10 @ X9) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.25  thf('31', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 1.06/1.25        | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      ((((sk_B) = (k1_xboole_0))
% 1.06/1.25        | ((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['31'])).
% 1.06/1.25  thf('33', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((sk_B) = (k1_xboole_0))
% 1.06/1.25        | (r1_tarski @ sk_A @ sk_C))),
% 1.06/1.25      inference('sup-', [status(thm)], ['32', '33'])).
% 1.06/1.25  thf('35', plain, (((r1_tarski @ sk_A @ sk_C) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['34'])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.06/1.25      inference('split', [status(esa)], ['27'])).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      ((((sk_B) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['35', '36'])).
% 1.06/1.25  thf('38', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('39', plain,
% 1.06/1.25      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.06/1.25         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.25  thf('40', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('41', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['39', '40'])).
% 1.06/1.25  thf('42', plain, (((r1_tarski @ sk_A @ sk_C))),
% 1.06/1.25      inference('simplify', [status(thm)], ['41'])).
% 1.06/1.25  thf('43', plain,
% 1.06/1.25      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 1.06/1.25      inference('split', [status(esa)], ['27'])).
% 1.06/1.25  thf('44', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.06/1.25  thf('45', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['28', '44'])).
% 1.06/1.25  thf('46', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['26', '45'])).
% 1.06/1.25  thf('47', plain,
% 1.06/1.25      (![X10 : $i, X11 : $i]:
% 1.06/1.25         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 1.06/1.25          | ((X10) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.25  thf('48', plain,
% 1.06/1.25      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['47'])).
% 1.06/1.25  thf('49', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('50', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('51', plain,
% 1.06/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X15 @ X17) @ X16)
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X15 @ X16) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X17 @ X16)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.06/1.25  thf('52', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['50', '51'])).
% 1.06/1.25  thf('53', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('54', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('55', plain,
% 1.06/1.25      (((k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.06/1.25      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.06/1.25  thf('56', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.06/1.25  thf('57', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('58', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf('59', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 1.06/1.25           (k2_zfmisc_1 @ k1_xboole_0 @ X1))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['57', '58'])).
% 1.06/1.25  thf('60', plain,
% 1.06/1.25      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['47'])).
% 1.06/1.25  thf('61', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('62', plain,
% 1.06/1.25      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X18 @ (k2_xboole_0 @ X15 @ X17))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X15) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X18 @ X17)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.06/1.25  thf('63', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X0 @ X2)
% 1.06/1.25           = (k2_zfmisc_1 @ X0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X1))))),
% 1.06/1.25      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 1.06/1.25  thf('64', plain,
% 1.06/1.25      (![X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X2 @ X1)
% 1.06/1.25           = (k2_zfmisc_1 @ X2 @ (k2_xboole_0 @ X1 @ k1_xboole_0)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['56', '63'])).
% 1.06/1.25  thf('65', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('66', plain,
% 1.06/1.25      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X18 @ (k2_xboole_0 @ X15 @ X17))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X15) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X18 @ X17)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.06/1.25  thf('67', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1) @ k1_xboole_0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['65', '66'])).
% 1.06/1.25  thf('68', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X1 @ X0)
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['64', '67'])).
% 1.06/1.25  thf('69', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.06/1.25  thf('70', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.25  thf('71', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['69', '70'])).
% 1.06/1.25  thf('72', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['71'])).
% 1.06/1.25  thf('73', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['68', '72'])).
% 1.06/1.25  thf('74', plain,
% 1.06/1.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.06/1.25         (((X12) = (k1_xboole_0))
% 1.06/1.25          | (r1_tarski @ X13 @ X14)
% 1.06/1.25          | ~ (r1_tarski @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 1.06/1.25               (k2_zfmisc_1 @ X12 @ X14)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 1.06/1.25  thf('75', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X0) | ((X1) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['73', '74'])).
% 1.06/1.25  thf('76', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.06/1.25      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.06/1.25  thf('77', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((r1_tarski @ X0 @ X1) | (r1_tarski @ X2 @ X2))),
% 1.06/1.25      inference('sup+', [status(thm)], ['75', '76'])).
% 1.06/1.25  thf('78', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.06/1.25      inference('condensation', [status(thm)], ['77'])).
% 1.06/1.25  thf('79', plain,
% 1.06/1.25      (![X0 : $i, X2 : $i]:
% 1.06/1.25         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.25  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.25  thf('81', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('82', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['80', '81'])).
% 1.06/1.25  thf('83', plain,
% 1.06/1.25      (![X7 : $i, X8 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.06/1.25  thf('84', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf('85', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 1.06/1.25           (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X3) @ X0))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['83', '84'])).
% 1.06/1.25  thf('86', plain,
% 1.06/1.25      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['47'])).
% 1.06/1.25  thf('87', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ 
% 1.06/1.25           (k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X3) @ X0))
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.06/1.25      inference('demod', [status(thm)], ['85', '86'])).
% 1.06/1.25  thf('88', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1) @ k1_xboole_0)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ X2 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['82', '87'])).
% 1.06/1.25  thf('89', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['78', '79'])).
% 1.06/1.25  thf('91', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('92', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.06/1.25      inference('sup+', [status(thm)], ['90', '91'])).
% 1.06/1.25  thf('93', plain,
% 1.06/1.25      (![X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X2 @ X1)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.06/1.25      inference('demod', [status(thm)], ['88', '89', '92'])).
% 1.06/1.25  thf('94', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k1_xboole_0)
% 1.06/1.25           = (k2_zfmisc_1 @ X0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D))))),
% 1.06/1.25      inference('demod', [status(thm)],
% 1.06/1.25                ['11', '12', '14', '15', '46', '48', '49', '55', '93'])).
% 1.06/1.25  thf('95', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('96', plain,
% 1.06/1.25      (((k4_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k1_xboole_0))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('97', plain,
% 1.06/1.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ X23 @ X25) @ (k2_zfmisc_1 @ X24 @ X26))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ (k4_xboole_0 @ X23 @ X24) @ X25) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X23 @ (k4_xboole_0 @ X25 @ X26))))),
% 1.06/1.25      inference('cnf', [status(esa)], [t126_zfmisc_1])).
% 1.06/1.25  thf('98', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X1) @ 
% 1.06/1.25           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 1.06/1.25              (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25               (k4_xboole_0 @ X1 @ X0))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['96', '97'])).
% 1.06/1.25  thf('99', plain,
% 1.06/1.25      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['47'])).
% 1.06/1.25  thf('100', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X1) @ 
% 1.06/1.25           (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25               (k4_xboole_0 @ X1 @ X0))))),
% 1.06/1.25      inference('demod', [status(thm)], ['98', '99'])).
% 1.06/1.25  thf('101', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k4_xboole_0 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) @ 
% 1.06/1.25           k1_xboole_0)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 1.06/1.25               (k4_xboole_0 @ X0 @ k1_xboole_0))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['95', '100'])).
% 1.06/1.25  thf('102', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('103', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.25  thf('104', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25              (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0)))),
% 1.06/1.25      inference('demod', [status(thm)], ['101', '102', '103'])).
% 1.06/1.25  thf('105', plain,
% 1.06/1.25      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['13'])).
% 1.06/1.25  thf('106', plain,
% 1.06/1.25      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X18 @ (k2_xboole_0 @ X15 @ X17))
% 1.06/1.25           = (k2_xboole_0 @ (k2_zfmisc_1 @ X18 @ X15) @ 
% 1.06/1.25              (k2_zfmisc_1 @ X18 @ X17)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.06/1.25  thf('107', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['105', '106'])).
% 1.06/1.25  thf('108', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         (((X9) = (k1_xboole_0))
% 1.06/1.25          | ((X10) = (k1_xboole_0))
% 1.06/1.25          | ((k2_zfmisc_1 @ X10 @ X9) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.25  thf('109', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (((k2_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.06/1.25            != (k1_xboole_0))
% 1.06/1.25          | ((X1) = (k1_xboole_0))
% 1.06/1.25          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['107', '108'])).
% 1.06/1.25  thf('110', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) != (k1_xboole_0))
% 1.06/1.25          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 1.06/1.25          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['104', '109'])).
% 1.06/1.25  thf('111', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('112', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0) != (k1_xboole_0))
% 1.06/1.25          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.06/1.25      inference('simplify_reflect-', [status(thm)], ['110', '111'])).
% 1.06/1.25  thf('113', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((k2_xboole_0 @ k1_xboole_0 @ 
% 1.06/1.25            (k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D))) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['94', '112'])).
% 1.06/1.25  thf('114', plain,
% 1.06/1.25      (![X1 : $i, X2 : $i]:
% 1.06/1.25         ((k2_zfmisc_1 @ X2 @ X1)
% 1.06/1.25           = (k2_xboole_0 @ k1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.06/1.25      inference('demod', [status(thm)], ['88', '89', '92'])).
% 1.06/1.25  thf('115', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0)))),
% 1.06/1.25      inference('demod', [status(thm)], ['113', '114'])).
% 1.06/1.25  thf('116', plain,
% 1.06/1.25      (((k2_zfmisc_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_D)) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['115'])).
% 1.06/1.25  thf('117', plain,
% 1.06/1.25      (![X9 : $i, X10 : $i]:
% 1.06/1.25         (((X9) = (k1_xboole_0))
% 1.06/1.25          | ((X10) = (k1_xboole_0))
% 1.06/1.25          | ((k2_zfmisc_1 @ X10 @ X9) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.06/1.25  thf('118', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((sk_A) = (k1_xboole_0))
% 1.06/1.25        | ((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['116', '117'])).
% 1.06/1.25  thf('119', plain,
% 1.06/1.25      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 1.06/1.25        | ((sk_A) = (k1_xboole_0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['118'])).
% 1.06/1.25  thf('120', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.25  thf('121', plain,
% 1.06/1.25      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.25        | ((sk_A) = (k1_xboole_0))
% 1.06/1.25        | (r1_tarski @ sk_B @ sk_D))),
% 1.06/1.25      inference('sup-', [status(thm)], ['119', '120'])).
% 1.06/1.25  thf('122', plain, (((r1_tarski @ sk_B @ sk_D) | ((sk_A) = (k1_xboole_0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['121'])).
% 1.06/1.25  thf('123', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['28', '44'])).
% 1.06/1.25  thf('124', plain, (((sk_A) = (k1_xboole_0))),
% 1.06/1.25      inference('clc', [status(thm)], ['122', '123'])).
% 1.06/1.25  thf('125', plain,
% 1.06/1.25      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['47'])).
% 1.06/1.25  thf('126', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.06/1.25      inference('demod', [status(thm)], ['0', '124', '125'])).
% 1.06/1.25  thf('127', plain, ($false), inference('simplify', [status(thm)], ['126'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.09/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
