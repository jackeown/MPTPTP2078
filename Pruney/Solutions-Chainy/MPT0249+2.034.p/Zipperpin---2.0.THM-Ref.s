%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hqrx3BkR0i

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:43 EST 2020

% Result     : Theorem 3.14s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  258 (11849 expanded)
%              Number of leaves         :   26 (4103 expanded)
%              Depth                    :   29
%              Number of atoms          : 2221 (108414 expanded)
%              Number of equality atoms :  225 (11356 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X20 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X14 ) @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C )
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('25',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ sk_C )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X14 ) @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X14 ) @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_B ) @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('39',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X27 ) @ X28 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X28 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('48',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) @ X0 ) )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('71',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X27 ) @ X28 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X28 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('75',plain,(
    ! [X19: $i] :
      ( ( r1_xboole_0 @ X19 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('76',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X27 ) @ X28 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X28 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('80',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('87',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('100',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','105'])).

thf('107',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','108'])).

thf('110',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('113',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('117',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('119',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('120',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['109','110','117','118','119','120'])).

thf('122',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('126',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85','86','128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74','132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ X0 ) )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('139',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X29 @ X27 ) @ X28 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X28 ) @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('150',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('153',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','150'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['142','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('161',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('162',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['84','85','86','128','129','130','131'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('165',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162','163','164'])).

thf('166',plain,
    ( ( k1_xboole_0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['137','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('168',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('171',plain,
    ( ( k1_xboole_0
      = ( k2_xboole_0 @ sk_B @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('172',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('173',plain,
    ( ( k1_xboole_0
      = ( k2_xboole_0 @ sk_B @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('175',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('176',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('178',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k1_xboole_0
      = ( k2_xboole_0 @ sk_B @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['173','178'])).

thf('180',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('181',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('182',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ X5 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ ( sk_D @ X1 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( sk_D @ X0 @ X0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( r1_tarski @ X4 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ X0 )
      | ~ ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('188',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( ( k1_tarski @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['179','190'])).

thf('192',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

thf('194',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['12','193'])).

thf('195',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

thf('196',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('204',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('205',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X1 ) ) @ X0 )
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','211'])).

thf('213',plain,(
    ! [X55: $i,X57: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X55 ) @ X57 )
      | ~ ( r2_hidden @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ sk_B ) )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('219',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('221',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
    | ( ( k1_tarski @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

thf('223',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('simplify_reflect-',[status(thm)],['191','192'])).

thf('224',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( sk_B = sk_C ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['224','225'])).

thf('227',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['216','226'])).

thf('228',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup+',[status(thm)],['194','227'])).

thf('229',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['228','229'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hqrx3BkR0i
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.14/3.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.14/3.35  % Solved by: fo/fo7.sh
% 3.14/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.14/3.35  % done 5005 iterations in 2.881s
% 3.14/3.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.14/3.35  % SZS output start Refutation
% 3.14/3.35  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.14/3.35  thf(sk_B_type, type, sk_B: $i).
% 3.14/3.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.14/3.35  thf(sk_A_type, type, sk_A: $i).
% 3.14/3.35  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.14/3.35  thf(sk_C_type, type, sk_C: $i).
% 3.14/3.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.14/3.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.14/3.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.14/3.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.14/3.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.14/3.35  thf(t39_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.35  thf('0', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf(t41_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.14/3.35       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.14/3.35  thf('1', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('2', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 3.14/3.35           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['0', '1'])).
% 3.14/3.35  thf('3', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('4', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 3.14/3.35           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['2', '3'])).
% 3.14/3.35  thf(t82_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 3.14/3.35  thf('5', plain,
% 3.14/3.35      (![X25 : $i, X26 : $i]:
% 3.14/3.35         (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X26 @ X25))),
% 3.14/3.35      inference('cnf', [status(esa)], [t82_xboole_1])).
% 3.14/3.35  thf(t66_xboole_1, axiom,
% 3.14/3.35    (![A:$i]:
% 3.14/3.35     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 3.14/3.35       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 3.14/3.35  thf('6', plain,
% 3.14/3.35      (![X20 : $i]: (((X20) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X20 @ X20))),
% 3.14/3.35      inference('cnf', [status(esa)], [t66_xboole_1])).
% 3.14/3.35  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['5', '6'])).
% 3.14/3.35  thf('8', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['4', '7'])).
% 3.14/3.35  thf(t44_zfmisc_1, conjecture,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.14/3.35          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.14/3.35          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 3.14/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.14/3.35    (~( ![A:$i,B:$i,C:$i]:
% 3.14/3.35        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.14/3.35             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 3.14/3.35             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 3.14/3.35    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 3.14/3.35  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('10', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('11', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C)
% 3.14/3.35           = (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['9', '10'])).
% 3.14/3.35  thf('12', plain,
% 3.14/3.35      (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['8', '11'])).
% 3.14/3.35  thf(t46_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.14/3.35  thf('13', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 3.14/3.35      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.14/3.35  thf('14', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('15', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X14) @ X15) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['13', '14'])).
% 3.14/3.35  thf('16', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('17', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['15', '16'])).
% 3.14/3.35  thf('18', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('19', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['5', '6'])).
% 3.14/3.35  thf('21', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('22', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.14/3.35           = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['20', '21'])).
% 3.14/3.35  thf('23', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ 
% 3.14/3.35           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) @ X0)
% 3.14/3.35           = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['19', '22'])).
% 3.14/3.35  thf('24', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C)
% 3.14/3.35           = (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['9', '10'])).
% 3.14/3.35  thf('25', plain,
% 3.14/3.35      (((k4_xboole_0 @ k1_xboole_0 @ sk_C)
% 3.14/3.35         = (k4_xboole_0 @ 
% 3.14/3.35            (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ sk_B) @ 
% 3.14/3.35            (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['23', '24'])).
% 3.14/3.35  thf('26', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X14) @ X15) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['13', '14'])).
% 3.14/3.35  thf('27', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X14) @ X15) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['13', '14'])).
% 3.14/3.35  thf('28', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('29', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('30', plain,
% 3.14/3.35      (((k1_xboole_0)
% 3.14/3.35         = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_B) @ sk_B) @ 
% 3.14/3.35            (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('demod', [status(thm)], ['25', '28', '29'])).
% 3.14/3.35  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf(t6_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.35  thf('32', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('33', plain,
% 3.14/3.35      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('sup+', [status(thm)], ['31', '32'])).
% 3.14/3.35  thf('34', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('35', plain,
% 3.14/3.35      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 3.14/3.35      inference('demod', [status(thm)], ['33', '34'])).
% 3.14/3.35  thf('36', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('37', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 3.14/3.35           = (k4_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['35', '36'])).
% 3.14/3.35  thf('38', plain,
% 3.14/3.35      (((k1_xboole_0)
% 3.14/3.35         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_B) @ (k1_tarski @ sk_A)))),
% 3.14/3.35      inference('demod', [status(thm)], ['30', '37'])).
% 3.14/3.35  thf(l27_zfmisc_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.14/3.35  thf('39', plain,
% 3.14/3.35      (![X53 : $i, X54 : $i]:
% 3.14/3.35         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 3.14/3.35      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.14/3.35  thf(t87_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ( r1_xboole_0 @ A @ B ) =>
% 3.14/3.35       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 3.14/3.35         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 3.14/3.35  thf('40', plain,
% 3.14/3.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.14/3.35         (~ (r1_xboole_0 @ X27 @ X28)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X29 @ X27) @ X28)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X29 @ X28) @ X27)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t87_xboole_1])).
% 3.14/3.35  thf('41', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((r2_hidden @ X1 @ X0)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))))),
% 3.14/3.35      inference('sup-', [status(thm)], ['39', '40'])).
% 3.14/3.35  thf('42', plain,
% 3.14/3.35      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 3.14/3.35          = (k1_xboole_0))
% 3.14/3.35        | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('sup+', [status(thm)], ['38', '41'])).
% 3.14/3.35  thf('43', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('44', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 3.14/3.35      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.14/3.35  thf('45', plain,
% 3.14/3.35      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['43', '44'])).
% 3.14/3.35  thf('46', plain,
% 3.14/3.35      ((((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 3.14/3.35        | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('demod', [status(thm)], ['42', '45'])).
% 3.14/3.35  thf('47', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('48', plain,
% 3.14/3.35      ((((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 3.14/3.35          = (k2_xboole_0 @ k1_xboole_0 @ sk_B))
% 3.14/3.35        | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('sup+', [status(thm)], ['46', '47'])).
% 3.14/3.35  thf('49', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.14/3.35           = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['20', '21'])).
% 3.14/3.35  thf('50', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('51', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('52', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.14/3.35           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['50', '51'])).
% 3.14/3.35  thf('53', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('54', plain,
% 3.14/3.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 3.14/3.35           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.14/3.35  thf('55', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X1) @ X0)
% 3.14/3.35           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['52', '53', '54'])).
% 3.14/3.35  thf('56', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.14/3.35           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X1) @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['49', '55'])).
% 3.14/3.35  thf('57', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('58', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X1) @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['56', '57'])).
% 3.14/3.35  thf('59', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((k1_xboole_0)
% 3.14/3.35            = (k4_xboole_0 @ 
% 3.14/3.35               (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0) @ 
% 3.14/3.35               X0))
% 3.14/3.35          | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('sup+', [status(thm)], ['48', '58'])).
% 3.14/3.35  thf('60', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('61', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf(t4_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 3.14/3.35       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.14/3.35  thf('62', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('63', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 3.14/3.35           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['61', '62'])).
% 3.14/3.35  thf('64', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('65', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('66', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('67', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['60', '66'])).
% 3.14/3.35  thf('68', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('69', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.14/3.35           = (k2_xboole_0 @ X1 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.14/3.35  thf('70', plain,
% 3.14/3.35      (![X25 : $i, X26 : $i]:
% 3.14/3.35         (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X26 @ X25))),
% 3.14/3.35      inference('cnf', [status(esa)], [t82_xboole_1])).
% 3.14/3.35  thf('71', plain,
% 3.14/3.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.14/3.35         (~ (r1_xboole_0 @ X27 @ X28)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X29 @ X27) @ X28)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X29 @ X28) @ X27)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t87_xboole_1])).
% 3.14/3.35  thf('72', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 3.14/3.35           (k4_xboole_0 @ X1 @ X0))
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 3.14/3.35              (k4_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['70', '71'])).
% 3.14/3.35  thf('73', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ 
% 3.14/3.35           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 3.14/3.35           (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.14/3.35              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['69', '72'])).
% 3.14/3.35  thf('74', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('75', plain,
% 3.14/3.35      (![X19 : $i]: ((r1_xboole_0 @ X19 @ X19) | ((X19) != (k1_xboole_0)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t66_xboole_1])).
% 3.14/3.35  thf('76', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.14/3.35      inference('simplify', [status(thm)], ['75'])).
% 3.14/3.35  thf('77', plain,
% 3.14/3.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.14/3.35         (~ (r1_xboole_0 @ X27 @ X28)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X29 @ X27) @ X28)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X29 @ X28) @ X27)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t87_xboole_1])).
% 3.14/3.35  thf('78', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['76', '77'])).
% 3.14/3.35  thf('79', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('80', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('81', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 3.14/3.35           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['79', '80'])).
% 3.14/3.35  thf('82', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('83', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 3.14/3.35           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 3.14/3.35      inference('demod', [status(thm)], ['81', '82'])).
% 3.14/3.35  thf('84', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35           (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1))
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k2_xboole_0 @ 
% 3.14/3.35               (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) @ 
% 3.14/3.35               X1)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['78', '83'])).
% 3.14/3.35  thf('85', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('86', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('87', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('88', plain,
% 3.14/3.35      (![X14 : $i, X15 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 3.14/3.35      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.14/3.35  thf('89', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('90', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['88', '89'])).
% 3.14/3.35  thf('91', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 3.14/3.35      inference('sup+', [status(thm)], ['87', '90'])).
% 3.14/3.35  thf('92', plain,
% 3.14/3.35      (![X21 : $i, X22 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22))
% 3.14/3.35           = (k2_xboole_0 @ X21 @ X22))),
% 3.14/3.35      inference('cnf', [status(esa)], [t6_xboole_1])).
% 3.14/3.35  thf('93', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['91', '92'])).
% 3.14/3.35  thf('94', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('95', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('96', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 3.14/3.35           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('demod', [status(thm)], ['93', '94', '95'])).
% 3.14/3.35  thf('97', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('98', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf(d10_xboole_0, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.14/3.35  thf('99', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.14/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.14/3.35  thf('100', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf(t44_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.14/3.35       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.14/3.35  thf('101', plain,
% 3.14/3.35      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.14/3.35         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 3.14/3.35          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 3.14/3.35      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.14/3.35  thf('102', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['100', '101'])).
% 3.14/3.35  thf('103', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('104', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['102', '103'])).
% 3.14/3.35  thf('105', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 3.14/3.35          (k2_xboole_0 @ X1 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['98', '104'])).
% 3.14/3.35  thf('106', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 3.14/3.35          (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['97', '105'])).
% 3.14/3.35  thf('107', plain,
% 3.14/3.35      (![X0 : $i, X2 : $i]:
% 3.14/3.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.14/3.35  thf('108', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 3.14/3.35             (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35          | ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 3.14/3.35              = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['106', '107'])).
% 3.14/3.35  thf('109', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ 
% 3.14/3.35             (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) @ 
% 3.14/3.35             (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))
% 3.14/3.35          | ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.14/3.35              = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0))))),
% 3.14/3.35      inference('sup-', [status(thm)], ['96', '108'])).
% 3.14/3.35  thf('110', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('111', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['76', '77'])).
% 3.14/3.35  thf('112', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.14/3.35           = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['20', '21'])).
% 3.14/3.35  thf('113', plain,
% 3.14/3.35      (((k4_xboole_0 @ 
% 3.14/3.35         (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0) @ 
% 3.14/3.35         k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['111', '112'])).
% 3.14/3.35  thf('114', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('115', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['76', '77'])).
% 3.14/3.35  thf('116', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('117', plain,
% 3.14/3.35      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 3.14/3.35  thf('118', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['102', '103'])).
% 3.14/3.35  thf('119', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('120', plain,
% 3.14/3.35      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 3.14/3.35  thf('121', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.14/3.35      inference('demod', [status(thm)],
% 3.14/3.35                ['109', '110', '117', '118', '119', '120'])).
% 3.14/3.35  thf('122', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('123', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k2_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['121', '122'])).
% 3.14/3.35  thf('124', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('125', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('126', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('127', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('128', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ X1)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 3.14/3.35  thf('129', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('130', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('131', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ X1)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 3.14/3.35  thf('132', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ X1)
% 3.14/3.35           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 3.14/3.35      inference('demod', [status(thm)],
% 3.14/3.35                ['84', '85', '86', '128', '129', '130', '131'])).
% 3.14/3.35  thf('133', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('134', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['73', '74', '132', '133'])).
% 3.14/3.35  thf('135', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 3.14/3.35           = (k2_xboole_0 @ X1 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['67', '68'])).
% 3.14/3.35  thf('136', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ X0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['134', '135'])).
% 3.14/3.35  thf('137', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((k1_xboole_0)
% 3.14/3.35            = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ X0))
% 3.14/3.35          | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('demod', [status(thm)], ['59', '136'])).
% 3.14/3.35  thf('138', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('139', plain,
% 3.14/3.35      (![X25 : $i, X26 : $i]:
% 3.14/3.35         (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ (k4_xboole_0 @ X26 @ X25))),
% 3.14/3.35      inference('cnf', [status(esa)], [t82_xboole_1])).
% 3.14/3.35  thf('140', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)),
% 3.14/3.35      inference('sup+', [status(thm)], ['138', '139'])).
% 3.14/3.35  thf('141', plain,
% 3.14/3.35      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.14/3.35         (~ (r1_xboole_0 @ X27 @ X28)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X29 @ X27) @ X28)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X29 @ X28) @ X27)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t87_xboole_1])).
% 3.14/3.35  thf('142', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ 
% 3.14/3.35           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ k1_xboole_0) @ 
% 3.14/3.35              (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['140', '141'])).
% 3.14/3.35  thf('143', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('144', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('145', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.14/3.35           = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['20', '21'])).
% 3.14/3.35  thf('146', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0) @ 
% 3.14/3.35           k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['144', '145'])).
% 3.14/3.35  thf('147', plain,
% 3.14/3.35      (![X6 : $i, X7 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.14/3.35           = (k2_xboole_0 @ X6 @ X7))),
% 3.14/3.35      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.14/3.35  thf('148', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['146', '147'])).
% 3.14/3.35  thf('149', plain,
% 3.14/3.35      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 3.14/3.35  thf('150', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0)))),
% 3.14/3.35      inference('demod', [status(thm)], ['148', '149'])).
% 3.14/3.35  thf('151', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['143', '150'])).
% 3.14/3.35  thf('152', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['102', '103'])).
% 3.14/3.35  thf('153', plain,
% 3.14/3.35      (![X0 : $i, X2 : $i]:
% 3.14/3.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.14/3.35  thf('154', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 3.14/3.35          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['152', '153'])).
% 3.14/3.35  thf('155', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ k1_xboole_0 @ 
% 3.14/3.35             (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))
% 3.14/3.35          | ((k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['151', '154'])).
% 3.14/3.35  thf('156', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 3.14/3.35      inference('sup+', [status(thm)], ['143', '150'])).
% 3.14/3.35  thf('157', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ k1_xboole_0 @ 
% 3.14/3.35             (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))
% 3.14/3.35          | ((k1_xboole_0)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)))),
% 3.14/3.35      inference('demod', [status(thm)], ['155', '156'])).
% 3.14/3.35  thf('158', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ k1_xboole_0 @ 
% 3.14/3.35             (k2_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 3.14/3.35               (k4_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 3.14/3.35              k1_xboole_0))
% 3.14/3.35          | ((k1_xboole_0)
% 3.14/3.35              = (k4_xboole_0 @ 
% 3.14/3.35                 (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) @ 
% 3.14/3.35                 (k4_xboole_0 @ X0 @ k1_xboole_0))))),
% 3.14/3.35      inference('sup-', [status(thm)], ['142', '157'])).
% 3.14/3.35  thf('159', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 3.14/3.35           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['2', '3'])).
% 3.14/3.35  thf('160', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['4', '7'])).
% 3.14/3.35  thf('161', plain,
% 3.14/3.35      (((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 3.14/3.35  thf('162', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf('163', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ X1)
% 3.14/3.35           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 3.14/3.35      inference('demod', [status(thm)],
% 3.14/3.35                ['84', '85', '86', '128', '129', '130', '131'])).
% 3.14/3.35  thf('164', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ 
% 3.14/3.35           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ k1_xboole_0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ k1_xboole_0) @ 
% 3.14/3.35              (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['140', '141'])).
% 3.14/3.35  thf('165', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((k1_xboole_0)
% 3.14/3.35           = (k2_xboole_0 @ 
% 3.14/3.35              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 3.14/3.35              k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)],
% 3.14/3.35                ['158', '159', '160', '161', '162', '163', '164'])).
% 3.14/3.35  thf('166', plain,
% 3.14/3.35      ((((k1_xboole_0)
% 3.14/3.35          = (k2_xboole_0 @ 
% 3.14/3.35             (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B) @ k1_xboole_0) @ 
% 3.14/3.35             k1_xboole_0))
% 3.14/3.35        | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('sup+', [status(thm)], ['137', '165'])).
% 3.14/3.35  thf('167', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X1 @ X0)
% 3.14/3.35           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 3.14/3.35      inference('demod', [status(thm)], ['134', '135'])).
% 3.14/3.35  thf('168', plain,
% 3.14/3.35      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 3.14/3.35           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t4_xboole_1])).
% 3.14/3.35  thf('169', plain,
% 3.14/3.35      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['17', '18'])).
% 3.14/3.35  thf('170', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ X1)
% 3.14/3.35           = (k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.14/3.35      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 3.14/3.35  thf('171', plain,
% 3.14/3.35      ((((k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_B))
% 3.14/3.35        | (r2_hidden @ sk_A @ sk_B))),
% 3.14/3.35      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 3.14/3.35  thf(t37_zfmisc_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]:
% 3.14/3.35     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 3.14/3.35  thf('172', plain,
% 3.14/3.35      (![X55 : $i, X57 : $i]:
% 3.14/3.35         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 3.14/3.35      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 3.14/3.35  thf('173', plain,
% 3.14/3.35      ((((k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_B))
% 3.14/3.35        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 3.14/3.35      inference('sup-', [status(thm)], ['171', '172'])).
% 3.14/3.35  thf('174', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf(t7_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.14/3.35  thf('175', plain,
% 3.14/3.35      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 3.14/3.35      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.14/3.35  thf('176', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 3.14/3.35      inference('sup+', [status(thm)], ['174', '175'])).
% 3.14/3.35  thf('177', plain,
% 3.14/3.35      (![X0 : $i, X2 : $i]:
% 3.14/3.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.14/3.35  thf('178', plain,
% 3.14/3.35      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 3.14/3.35        | ((k1_tarski @ sk_A) = (sk_B)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['176', '177'])).
% 3.14/3.35  thf('179', plain,
% 3.14/3.35      ((((k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_B))
% 3.14/3.35        | ((k1_tarski @ sk_A) = (sk_B)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['173', '178'])).
% 3.14/3.35  thf('180', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf('181', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf(t14_xboole_1, axiom,
% 3.14/3.35    (![A:$i,B:$i,C:$i]:
% 3.14/3.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 3.14/3.35         ( ![D:$i]:
% 3.14/3.35           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 3.14/3.35             ( r1_tarski @ B @ D ) ) ) ) =>
% 3.14/3.35       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 3.14/3.35  thf('182', plain,
% 3.14/3.35      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.14/3.35         (~ (r1_tarski @ X3 @ X4)
% 3.14/3.35          | ~ (r1_tarski @ X5 @ X4)
% 3.14/3.35          | (r1_tarski @ X5 @ (sk_D @ X5 @ X4 @ X3))
% 3.14/3.35          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t14_xboole_1])).
% 3.14/3.35  thf('183', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (((X0) = (k2_xboole_0 @ X0 @ X1))
% 3.14/3.35          | (r1_tarski @ X1 @ (sk_D @ X1 @ X0 @ X0))
% 3.14/3.35          | ~ (r1_tarski @ X1 @ X0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['181', '182'])).
% 3.14/3.35  thf('184', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         ((r1_tarski @ X0 @ (sk_D @ X0 @ X0 @ X0))
% 3.14/3.35          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['180', '183'])).
% 3.14/3.35  thf('185', plain,
% 3.14/3.35      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.14/3.35         (~ (r1_tarski @ X3 @ X4)
% 3.14/3.35          | ~ (r1_tarski @ X5 @ X4)
% 3.14/3.35          | ~ (r1_tarski @ X4 @ (sk_D @ X5 @ X4 @ X3))
% 3.14/3.35          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 3.14/3.35      inference('cnf', [status(esa)], [t14_xboole_1])).
% 3.14/3.35  thf('186', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 3.14/3.35          | ((X0) = (k2_xboole_0 @ X0 @ X0))
% 3.14/3.35          | ~ (r1_tarski @ X0 @ X0)
% 3.14/3.35          | ~ (r1_tarski @ X0 @ X0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['184', '185'])).
% 3.14/3.35  thf('187', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf('188', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.14/3.35      inference('simplify', [status(thm)], ['99'])).
% 3.14/3.35  thf('189', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((X0) = (k2_xboole_0 @ X0 @ X0)) | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 3.14/3.35      inference('demod', [status(thm)], ['186', '187', '188'])).
% 3.14/3.35  thf('190', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('simplify', [status(thm)], ['189'])).
% 3.14/3.35  thf('191', plain,
% 3.14/3.35      ((((k1_xboole_0) = (sk_B)) | ((k1_tarski @ sk_A) = (sk_B)))),
% 3.14/3.35      inference('demod', [status(thm)], ['179', '190'])).
% 3.14/3.35  thf('192', plain, (((sk_B) != (k1_xboole_0))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('193', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 3.14/3.35  thf('194', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_B))),
% 3.14/3.35      inference('demod', [status(thm)], ['12', '193'])).
% 3.14/3.35  thf('195', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 3.14/3.35  thf('196', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('simplify', [status(thm)], ['189'])).
% 3.14/3.35  thf('197', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('198', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 3.14/3.35          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['152', '153'])).
% 3.14/3.35  thf('199', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.14/3.35             (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35          | ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35              = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['197', '198'])).
% 3.14/3.35  thf('200', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 3.14/3.35           = (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 3.14/3.35  thf('201', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ 
% 3.14/3.35             (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35          | ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.14/3.35      inference('demod', [status(thm)], ['199', '200'])).
% 3.14/3.35  thf('202', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 3.14/3.35          | ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['196', '201'])).
% 3.14/3.35  thf('203', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['102', '103'])).
% 3.14/3.35  thf('204', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 3.14/3.35      inference('simplify', [status(thm)], ['189'])).
% 3.14/3.35  thf('205', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['202', '203', '204'])).
% 3.14/3.35  thf('206', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.14/3.35         ((r2_hidden @ X1 @ X0)
% 3.14/3.35          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k1_tarski @ X1)) @ X0)
% 3.14/3.35              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k1_tarski @ X1))))),
% 3.14/3.35      inference('sup-', [status(thm)], ['39', '40'])).
% 3.14/3.35  thf('207', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X1)) @ X0)
% 3.14/3.35            = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 3.14/3.35          | (r2_hidden @ X1 @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['205', '206'])).
% 3.14/3.35  thf('208', plain,
% 3.14/3.35      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['26', '27'])).
% 3.14/3.35  thf('209', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (((k2_xboole_0 @ k1_xboole_0 @ X0)
% 3.14/3.35            = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 3.14/3.35          | (r2_hidden @ X1 @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['207', '208'])).
% 3.14/3.35  thf('210', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['202', '203', '204'])).
% 3.14/3.35  thf('211', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]:
% 3.14/3.35         (((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 3.14/3.35          | (r2_hidden @ X1 @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['209', '210'])).
% 3.14/3.35  thf('212', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((X0) = (k4_xboole_0 @ X0 @ sk_B)) | (r2_hidden @ sk_A @ X0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['195', '211'])).
% 3.14/3.35  thf('213', plain,
% 3.14/3.35      (![X55 : $i, X57 : $i]:
% 3.14/3.35         ((r1_tarski @ (k1_tarski @ X55) @ X57) | ~ (r2_hidden @ X55 @ X57))),
% 3.14/3.35      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 3.14/3.35  thf('214', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((X0) = (k4_xboole_0 @ X0 @ sk_B))
% 3.14/3.35          | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 3.14/3.35      inference('sup-', [status(thm)], ['212', '213'])).
% 3.14/3.35  thf('215', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 3.14/3.35  thf('216', plain,
% 3.14/3.35      (![X0 : $i]:
% 3.14/3.35         (((X0) = (k4_xboole_0 @ X0 @ sk_B)) | (r1_tarski @ sk_B @ X0))),
% 3.14/3.35      inference('demod', [status(thm)], ['214', '215'])).
% 3.14/3.35  thf('217', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('218', plain,
% 3.14/3.35      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 3.14/3.35      inference('demod', [status(thm)], ['102', '103'])).
% 3.14/3.35  thf('219', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 3.14/3.35      inference('sup+', [status(thm)], ['217', '218'])).
% 3.14/3.35  thf('220', plain,
% 3.14/3.35      (![X0 : $i, X2 : $i]:
% 3.14/3.35         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.14/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.14/3.35  thf('221', plain,
% 3.14/3.35      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C)
% 3.14/3.35        | ((k1_tarski @ sk_A) = (sk_C)))),
% 3.14/3.35      inference('sup-', [status(thm)], ['219', '220'])).
% 3.14/3.35  thf('222', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 3.14/3.35  thf('223', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['191', '192'])).
% 3.14/3.35  thf('224', plain, ((~ (r1_tarski @ sk_B @ sk_C) | ((sk_B) = (sk_C)))),
% 3.14/3.35      inference('demod', [status(thm)], ['221', '222', '223'])).
% 3.14/3.35  thf('225', plain, (((sk_B) != (sk_C))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('226', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['224', '225'])).
% 3.14/3.35  thf('227', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_B))),
% 3.14/3.35      inference('sup-', [status(thm)], ['216', '226'])).
% 3.14/3.35  thf('228', plain, (((sk_C) = (k1_xboole_0))),
% 3.14/3.35      inference('sup+', [status(thm)], ['194', '227'])).
% 3.14/3.35  thf('229', plain, (((sk_C) != (k1_xboole_0))),
% 3.14/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.14/3.35  thf('230', plain, ($false),
% 3.14/3.35      inference('simplify_reflect-', [status(thm)], ['228', '229'])).
% 3.14/3.35  
% 3.14/3.35  % SZS output end Refutation
% 3.14/3.35  
% 3.14/3.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
