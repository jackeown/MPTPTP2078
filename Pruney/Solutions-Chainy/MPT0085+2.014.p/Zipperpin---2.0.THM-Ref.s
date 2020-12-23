%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.45VUTXQrUt

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:27 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 144 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  542 (1145 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t78_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          = ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['34','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_2 )
 != ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['16','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.45VUTXQrUt
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 560 iterations in 0.266s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.72  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(t78_xboole_1, conjecture,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( r1_xboole_0 @ A @ B ) =>
% 0.53/0.72       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.53/0.72         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.72        ( ( r1_xboole_0 @ A @ B ) =>
% 0.53/0.72          ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.53/0.72            ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t78_xboole_1])).
% 0.53/0.72  thf('0', plain,
% 0.53/0.72      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.53/0.72         != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d3_tarski, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X1 : $i, X3 : $i]:
% 0.53/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.72  thf(t4_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.53/0.72          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.53/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.53/0.72  thf('4', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.53/0.72          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.72  thf('5', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['1', '4'])).
% 0.53/0.72  thf(t28_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X13 : $i, X14 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('7', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.53/0.72           = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.72  thf(t2_boole, axiom,
% 0.53/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['7', '8'])).
% 0.53/0.72  thf(t23_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.53/0.72       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.53/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 0.53/0.72              (k3_xboole_0 @ X10 @ X12)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['9', '10'])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('13', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.53/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 0.53/0.72              (k3_xboole_0 @ X10 @ X12)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.53/0.72  thf('14', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.72           = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['11', '14'])).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ k1_xboole_0 @ sk_C_2))
% 0.53/0.72         != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.53/0.72      inference('demod', [status(thm)], ['0', '15'])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      (![X1 : $i, X3 : $i]:
% 0.53/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.72  thf('18', plain,
% 0.53/0.72      (![X1 : $i, X3 : $i]:
% 0.53/0.72         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.72  thf('19', plain,
% 0.53/0.72      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.72  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.53/0.72  thf(t44_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.53/0.72       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.72         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.53/0.72          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 0.53/0.72      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      (![X13 : $i, X14 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.72  thf('25', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf('26', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.53/0.72      inference('simplify', [status(thm)], ['19'])).
% 0.53/0.72  thf('27', plain,
% 0.53/0.72      (![X13 : $i, X14 : $i]:
% 0.53/0.72         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.53/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.72  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.72           (k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['25', '30'])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.72           (k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))
% 0.53/0.72           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['31', '32'])).
% 0.53/0.72  thf('34', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ 
% 0.53/0.72           (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) @ X0)
% 0.53/0.72           = (k3_xboole_0 @ X0 @ 
% 0.53/0.72              (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))))),
% 0.53/0.72      inference('sup+', [status(thm)], ['24', '33'])).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.72  thf('36', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.53/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 0.53/0.72              (k3_xboole_0 @ X10 @ X12)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.53/0.72  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.53/0.72           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 0.53/0.72              (k3_xboole_0 @ X10 @ X12)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.53/0.72  thf('39', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.53/0.72           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['37', '38'])).
% 0.53/0.72  thf(t22_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X8 : $i, X9 : $i]:
% 0.53/0.72         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.53/0.72      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.53/0.72           (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (k3_xboole_0 @ X2 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['36', '41'])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.53/0.72           = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['35', '42'])).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['34', '43', '44'])).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf('47', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X0 @ 
% 0.53/0.72           (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))
% 0.53/0.72           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.72      inference('sup+', [status(thm)], ['45', '46'])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.72           = (X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.72  thf('49', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['47', '48'])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (((k3_xboole_0 @ sk_A @ sk_C_2) != (k3_xboole_0 @ sk_A @ sk_C_2))),
% 0.53/0.72      inference('demod', [status(thm)], ['16', '49'])).
% 0.53/0.72  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
