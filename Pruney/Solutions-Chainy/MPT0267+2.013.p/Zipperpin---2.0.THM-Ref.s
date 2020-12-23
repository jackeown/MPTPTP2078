%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h9CSUvle6S

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 126 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  570 (1169 expanded)
%              Number of equality atoms :   38 (  90 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k3_enumset1 @ X16 @ X16 @ X16 @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X14 @ X15 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ ( k2_tarski @ X17 @ X20 ) )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('8',plain,(
    ! [X17: $i,X20: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X17 @ X20 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( sk_A = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['14'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X22 ) )
      | ( X21 = X22 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('33',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['14'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = X0 )
        | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ X0 ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,
    ( ( sk_C_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) ) )
    | ( sk_A = sk_C_1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','28','29','30','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h9CSUvle6S
% 0.14/0.37  % Computer   : n021.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 19:39:50 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.57  % Solved by: fo/fo7.sh
% 0.23/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.57  % done 155 iterations in 0.096s
% 0.23/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.57  % SZS output start Refutation
% 0.23/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.23/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.23/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.57  thf(t64_zfmisc_1, conjecture,
% 0.23/0.57    (![A:$i,B:$i,C:$i]:
% 0.23/0.57     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.23/0.57       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.23/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.57        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.23/0.57          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.23/0.57    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.23/0.57  thf('0', plain,
% 0.23/0.57      ((((sk_A) != (sk_C_1))
% 0.23/0.57        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('1', plain,
% 0.23/0.57      (~ (((sk_A) = (sk_C_1))) | 
% 0.23/0.57       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.23/0.57      inference('split', [status(esa)], ['0'])).
% 0.23/0.57  thf(t72_enumset1, axiom,
% 0.23/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.23/0.57  thf('2', plain,
% 0.23/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.57         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.23/0.57           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.23/0.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.23/0.57  thf(t87_enumset1, axiom,
% 0.23/0.57    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.57  thf('3', plain,
% 0.23/0.57      (![X16 : $i]:
% 0.23/0.57         ((k3_enumset1 @ X16 @ X16 @ X16 @ X16 @ X16) = (k1_tarski @ X16))),
% 0.23/0.57      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.23/0.57  thf('4', plain,
% 0.23/0.57      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.23/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.23/0.57  thf(t77_enumset1, axiom,
% 0.23/0.57    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.23/0.57  thf('5', plain,
% 0.23/0.57      (![X14 : $i, X15 : $i]:
% 0.23/0.57         ((k2_enumset1 @ X14 @ X14 @ X14 @ X15) = (k2_tarski @ X14 @ X15))),
% 0.23/0.57      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.23/0.57  thf('6', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.23/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.57  thf(l45_zfmisc_1, axiom,
% 0.23/0.57    (![A:$i,B:$i,C:$i]:
% 0.23/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.23/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.23/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.57  thf('7', plain,
% 0.23/0.57      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.23/0.57         ((r1_tarski @ X19 @ (k2_tarski @ X17 @ X20))
% 0.23/0.57          | ((X19) != (k1_tarski @ X17)))),
% 0.23/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.23/0.57  thf('8', plain,
% 0.23/0.57      (![X17 : $i, X20 : $i]:
% 0.23/0.57         (r1_tarski @ (k1_tarski @ X17) @ (k2_tarski @ X17 @ X20))),
% 0.23/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.23/0.57  thf('9', plain,
% 0.23/0.57      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.23/0.57      inference('sup+', [status(thm)], ['6', '8'])).
% 0.23/0.57  thf('10', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.23/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.23/0.57  thf(t38_zfmisc_1, axiom,
% 0.23/0.57    (![A:$i,B:$i,C:$i]:
% 0.23/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.23/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.23/0.57  thf('11', plain,
% 0.23/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.57         ((r2_hidden @ X23 @ X24)
% 0.23/0.57          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 0.23/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.23/0.57  thf('12', plain,
% 0.23/0.57      (![X0 : $i, X1 : $i]:
% 0.23/0.57         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.23/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.23/0.57  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.57      inference('sup-', [status(thm)], ['9', '12'])).
% 0.23/0.57  thf('14', plain,
% 0.23/0.57      ((((sk_A) = (sk_C_1))
% 0.23/0.57        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.23/0.57        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('15', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.23/0.57      inference('split', [status(esa)], ['14'])).
% 0.23/0.57  thf('16', plain,
% 0.23/0.57      (((r2_hidden @ sk_A @ sk_B)
% 0.23/0.57        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.23/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.57  thf('17', plain,
% 0.23/0.57      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.23/0.57         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.23/0.57      inference('split', [status(esa)], ['16'])).
% 0.23/0.57  thf('18', plain,
% 0.23/0.57      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.57             (((sk_A) = (sk_C_1))))),
% 0.39/0.57      inference('sup+', [status(thm)], ['15', '17'])).
% 0.39/0.57  thf(d5_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.57           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.57          | ~ (r2_hidden @ X4 @ X2)
% 0.39/0.57          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ X2)
% 0.39/0.57          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.39/0.57         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.57             (((sk_A) = (sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (~ (((sk_A) = (sk_C_1))) | 
% 0.39/0.58       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.39/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.39/0.58      inference('split', [status(esa)], ['16'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X4 @ X3)
% 0.39/0.58          | (r2_hidden @ X4 @ X1)
% 0.39/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.39/0.58         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['23', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['14'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.58       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.58       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.39/0.58       (((sk_A) = (sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['14'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.58       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['16'])).
% 0.39/0.58  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.39/0.58  thf(t17_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) != ( B ) ) =>
% 0.39/0.58       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X21 : $i, X22 : $i]:
% 0.39/0.58         ((r1_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X22))
% 0.39/0.58          | ((X21) = (X22)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('split', [status(esa)], ['16'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.58          | (r2_hidden @ X0 @ X2)
% 0.39/0.58          | (r2_hidden @ X0 @ X3)
% 0.39/0.58          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.39/0.58          | (r2_hidden @ X0 @ X2)
% 0.39/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          ((r2_hidden @ sk_A @ X0)
% 0.39/0.58           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.39/0.58         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))))),
% 0.39/0.58      inference('split', [status(esa)], ['14'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.58             ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.58  thf(t3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.58            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.39/0.58          | ~ (r2_hidden @ X8 @ X9)
% 0.39/0.58          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (~ (r1_xboole_0 @ (k1_tarski @ sk_C_1) @ X0)
% 0.39/0.58           | ~ (r2_hidden @ sk_A @ X0)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.58             ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (((sk_C_1) = (X0)) | ~ (r2_hidden @ sk_A @ (k1_tarski @ X0))))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.58             ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      ((((sk_C_1) = (sk_A)))
% 0.39/0.58         <= (~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.58             ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '41'])).
% 0.39/0.58  thf('43', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((((sk_A) != (sk_A)))
% 0.39/0.58         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.39/0.58             ~
% 0.39/0.58             ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) & 
% 0.39/0.58             ((r2_hidden @ sk_A @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.39/0.58       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)))) | 
% 0.39/0.58       (((sk_A) = (sk_C_1)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.58  thf('46', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)],
% 0.39/0.58                ['1', '22', '28', '29', '30', '45'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
