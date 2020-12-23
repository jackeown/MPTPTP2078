%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zn0mXgVM1l

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 221 expanded)
%              Number of leaves         :   15 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  533 (2599 expanded)
%              Number of equality atoms :   25 (  78 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['16'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k3_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B ) )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
      & ( r1_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','15','32'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['2','15','32','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['16'])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','15','32','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['34','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zn0mXgVM1l
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:51:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 157 iterations in 0.081s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(t70_xboole_1, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.19/0.52            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.19/0.52       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.19/0.52            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.53        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.19/0.53               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.19/0.53          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.19/0.53               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 0.19/0.53        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.19/0.53        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.19/0.53         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.19/0.53       ~ ((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.19/0.53        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['3'])).
% 0.19/0.53  thf(t23_xboole_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.19/0.53       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.19/0.53           = (k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.19/0.53              (k3_xboole_0 @ X14 @ X16)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.19/0.53  thf(t4_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X9 : $i, X10 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X9 @ X10)
% 0.19/0.53          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf(d3_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.19/0.53       ( ![D:$i]:
% 0.19/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.53           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.53          | (r2_hidden @ X0 @ X2)
% 0.19/0.53          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.19/0.53         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X1 @ X0)
% 0.19/0.53          | (r2_hidden @ (sk_C @ X0 @ X1) @ 
% 0.19/0.53             (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['6', '8'])).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r2_hidden @ (sk_C @ X0 @ X2) @ 
% 0.19/0.53           (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.19/0.53          | (r1_xboole_0 @ X2 @ X0))),
% 0.19/0.53      inference('sup+', [status(thm)], ['5', '9'])).
% 0.19/0.53  thf('11', plain,
% 0.19/0.53      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.19/0.53         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.19/0.53          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.19/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X2 @ X0)
% 0.19/0.53          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['4', '12'])).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.19/0.53       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.19/0.53        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['16'])).
% 0.19/0.53  thf(d7_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      ((((k3_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.19/0.53           = (k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ 
% 0.19/0.53              (k3_xboole_0 @ X14 @ X16)))),
% 0.19/0.53      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      ((![X0 : $i]:
% 0.19/0.53          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 0.19/0.53            = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.53  thf(t1_boole, axiom,
% 0.19/0.53    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.53  thf('22', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.19/0.53      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      ((![X0 : $i]:
% 0.19/0.53          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 0.19/0.53            = (k3_xboole_0 @ sk_A @ X0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.19/0.53      inference('split', [status(esa)], ['3'])).
% 0.19/0.53  thf('25', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      ((((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.19/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain,
% 0.19/0.53      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.19/0.53             ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['23', '26'])).
% 0.19/0.53  thf('28', plain,
% 0.19/0.53      (![X6 : $i, X8 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('29', plain,
% 0.19/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.19/0.53             ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.53  thf('30', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) & 
% 0.19/0.53             ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.53  thf('31', plain,
% 0.19/0.53      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('split', [status(esa)], ['0'])).
% 0.19/0.53  thf('32', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.19/0.53       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.53  thf('33', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['2', '15', '32'])).
% 0.19/0.53  thf('34', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.19/0.53  thf('35', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('split', [status(esa)], ['3'])).
% 0.19/0.53  thf('36', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('37', plain,
% 0.19/0.53      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.53  thf('38', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.19/0.53       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['3'])).
% 0.19/0.53  thf('39', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['2', '15', '32', '38'])).
% 0.19/0.53  thf('40', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.19/0.53  thf('41', plain,
% 0.19/0.53      ((![X0 : $i]:
% 0.19/0.53          ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 0.19/0.53            = (k3_xboole_0 @ sk_A @ X0)))
% 0.19/0.53         <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.53  thf('42', plain,
% 0.19/0.53      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.19/0.53       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('split', [status(esa)], ['16'])).
% 0.19/0.53  thf('43', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.53      inference('sat_resolution*', [status(thm)], ['2', '15', '32', '42'])).
% 0.19/0.53  thf('44', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1))
% 0.19/0.53           = (k3_xboole_0 @ sk_A @ X0))),
% 0.19/0.53      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.19/0.53  thf('45', plain,
% 0.19/0.53      (![X6 : $i, X8 : $i]:
% 0.19/0.53         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.53  thf('46', plain,
% 0.19/0.53      (![X0 : $i]:
% 0.19/0.53         (((k3_xboole_0 @ sk_A @ X0) != (k1_xboole_0))
% 0.19/0.53          | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.53  thf('47', plain,
% 0.19/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.53        | (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['40', '46'])).
% 0.19/0.53  thf('48', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.53  thf('49', plain, ($false), inference('demod', [status(thm)], ['34', '48'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
