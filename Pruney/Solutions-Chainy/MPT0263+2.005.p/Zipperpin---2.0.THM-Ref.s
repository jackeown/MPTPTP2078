%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wf3TTQu1bV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:31 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 (  78 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   15
%              Number of atoms          :  438 ( 548 expanded)
%              Number of equality atoms :   42 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X41 != X40 )
      | ( r2_hidden @ X41 @ X42 )
      | ( X42
       != ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X40: $i] :
      ( r2_hidden @ X40 @ ( k1_tarski @ X40 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X51: $i,X53: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ X53 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X15 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k3_xboole_0 @ X19 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['26','30'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X51: $i,X53: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ X53 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wf3TTQu1bV
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 194 iterations in 0.102s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(d1_tarski, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.55         (((X41) != (X40))
% 0.36/0.55          | (r2_hidden @ X41 @ X42)
% 0.36/0.55          | ((X42) != (k1_tarski @ X40)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.55  thf('1', plain, (![X40 : $i]: (r2_hidden @ X40 @ (k1_tarski @ X40))),
% 0.36/0.55      inference('simplify', [status(thm)], ['0'])).
% 0.36/0.55  thf(d5_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.55       ( ![D:$i]:
% 0.36/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ X3)
% 0.36/0.55          | (r2_hidden @ X2 @ X4)
% 0.36/0.55          | (r2_hidden @ X2 @ X5)
% 0.36/0.55          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.55         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.36/0.55          | (r2_hidden @ X2 @ X4)
% 0.36/0.55          | ~ (r2_hidden @ X2 @ X3))),
% 0.36/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ X1)
% 0.36/0.55          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.36/0.55  thf(l35_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.55       ( r2_hidden @ A @ B ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X51 : $i, X53 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ (k1_tarski @ X51) @ X53) = (k1_xboole_0))
% 0.36/0.55          | ~ (r2_hidden @ X51 @ X53))),
% 0.36/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X1 @ X0)
% 0.36/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.55              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf(t48_xboole_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.55           = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X1 @ X0)
% 0.36/0.55          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.55  thf(t4_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X15 @ X16)
% 0.36/0.55          | (r2_hidden @ (sk_C_1 @ X16 @ X15) @ (k3_xboole_0 @ X15 @ X16)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.55  thf(t3_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.55  thf('11', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.55           = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf(t2_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.55  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.55           = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.36/0.55  thf('18', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.55  thf('19', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 0.36/0.55          | ~ (r1_xboole_0 @ X15 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.55          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.36/0.55          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.36/0.55          | (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)) @ k1_xboole_0)
% 0.36/0.55          | (r2_hidden @ X1 @ X0)
% 0.36/0.55          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X19 : $i]: ((k3_xboole_0 @ X19 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.55  thf(d7_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X8 : $i, X10 : $i]:
% 0.36/0.55         ((r1_xboole_0 @ X8 @ X10)
% 0.36/0.55          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.55  thf('30', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.36/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['26', '30'])).
% 0.36/0.55  thf(t58_zfmisc_1, conjecture,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.36/0.55       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i]:
% 0.36/0.55        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.36/0.55          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.36/0.55  thf('32', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('33', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X51 : $i, X53 : $i]:
% 0.36/0.55         (((k4_xboole_0 @ (k1_tarski @ X51) @ X53) = (k1_xboole_0))
% 0.36/0.55          | ~ (r2_hidden @ X51 @ X53))),
% 0.36/0.55      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.36/0.55           = (k3_xboole_0 @ X23 @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.36/0.55         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.36/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
