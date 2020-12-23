%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C9FzP3Da9Q

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 144 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  531 (1088 expanded)
%              Number of equality atoms :   61 ( 125 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X59: $i,X61: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X59 ) @ X61 )
      | ~ ( r2_hidden @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13','14','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X62 @ X63 ) )
      = ( k2_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X62 @ X63 ) )
      = ( k2_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','25','40'])).

thf('42',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27 != X26 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,(
    ! [X26: $i] :
      ( r2_hidden @ X26 @ ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['27','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C9FzP3Da9Q
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 304 iterations in 0.146s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.65  thf(t68_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65       ( r2_hidden @ A @ B ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i]:
% 0.46/0.65        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.65          ( r2_hidden @ A @ B ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.46/0.65        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.46/0.65       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B_1)
% 0.46/0.65        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('split', [status(esa)], ['3'])).
% 0.46/0.65  thf(l1_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X59 : $i, X61 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X59) @ X61) | ~ (r2_hidden @ X59 @ X61))),
% 0.46/0.65      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf(t12_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(t95_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k3_xboole_0 @ A @ B ) =
% 0.46/0.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k3_xboole_0 @ X22 @ X23)
% 0.46/0.65           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.46/0.65              (k2_xboole_0 @ X22 @ X23)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.46/0.65  thf(t91_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.46/0.65           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         ((k3_xboole_0 @ X22 @ X23)
% 0.46/0.65           = (k5_xboole_0 @ X22 @ 
% 0.46/0.65              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.46/0.65          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B_1 @ sk_B_1))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['8', '11'])).
% 0.46/0.65  thf(t92_xboole_1, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('13', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.65  thf(commutativity_k5_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.46/0.65  thf(t5_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('16', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13', '14', '17'])).
% 0.46/0.65  thf(t100_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X10 @ X11)
% 0.46/0.65           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.46/0.65          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.65         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.65         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))) & 
% 0.46/0.65             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.65       ~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.65  thf('26', plain, (~ ((r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.46/0.65  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.65         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.65      inference('split', [status(esa)], ['3'])).
% 0.46/0.65  thf(t39_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X15 : $i, X16 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.46/0.65           = (k2_xboole_0 @ X15 @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.46/0.65          = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.46/0.65         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.65      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf(commutativity_k2_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i]:
% 0.46/0.65         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.65  thf(l51_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X62 : $i, X63 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X62 @ X63)) = (k2_xboole_0 @ X62 @ X63))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X62 : $i, X63 : $i]:
% 0.46/0.65         ((k3_tarski @ (k2_tarski @ X62 @ X63)) = (k2_xboole_0 @ X62 @ X63))),
% 0.46/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf(t1_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('37', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.65  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 0.46/0.65         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '35', '38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))) | 
% 0.46/0.65       ((r2_hidden @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('split', [status(esa)], ['3'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['2', '25', '40'])).
% 0.46/0.65  thf('42', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.46/0.65  thf(d1_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (((X27) != (X26))
% 0.46/0.65          | (r2_hidden @ X27 @ X28)
% 0.46/0.65          | ((X28) != (k1_tarski @ X26)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.65  thf('44', plain, (![X26 : $i]: (r2_hidden @ X26 @ (k1_tarski @ X26))),
% 0.46/0.65      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.65  thf(d3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ X3)
% 0.46/0.65          | (r2_hidden @ X2 @ X4)
% 0.46/0.65          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.46/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.46/0.65      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '46'])).
% 0.46/0.65  thf('48', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.46/0.65      inference('sup+', [status(thm)], ['42', '47'])).
% 0.46/0.65  thf('49', plain, ($false), inference('demod', [status(thm)], ['27', '48'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
