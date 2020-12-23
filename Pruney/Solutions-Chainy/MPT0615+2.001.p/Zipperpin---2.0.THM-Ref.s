%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wFtwavi5Yh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  451 ( 730 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t219_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
          <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
            <=> ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t219_relat_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X26: $i] :
      ( ( ( k7_relat_1 @ X26 @ ( k1_relat_1 @ X26 ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k7_relat_1 @ X19 @ X20 ) @ ( k7_relat_1 @ X18 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_A )
        | ( r1_tarski @ ( k7_relat_1 @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_B @ X0 ) )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k7_relat_1 @ sk_A @ X0 ) @ ( k7_relat_1 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ( ( k7_relat_1 @ X24 @ X25 )
        = X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t107_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
        = ( k2_xboole_0 @ ( k7_relat_1 @ X21 @ X22 ) @ ( k7_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t107_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k7_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k7_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_A @ X0 )
        | ~ ( r1_tarski @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','15','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wFtwavi5Yh
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:42:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 115 iterations in 0.051s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(t219_relat_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50             ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( v1_relat_1 @ B ) =>
% 0.21/0.50              ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50                ( r1_tarski @ A @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t219_relat_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.21/0.50        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.21/0.50       ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf(t98_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X26 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X26 @ (k1_relat_1 @ X26)) = (X26))
% 0.21/0.50          | ~ (v1_relat_1 @ X26))),
% 0.21/0.50      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.21/0.50        | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf(t105_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ C ) =>
% 0.21/0.50           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.50             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X18)
% 0.21/0.50          | (r1_tarski @ (k7_relat_1 @ X19 @ X20) @ (k7_relat_1 @ X18 @ X20))
% 0.21/0.50          | ~ (r1_tarski @ X19 @ X18)
% 0.21/0.50          | ~ (v1_relat_1 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (v1_relat_1 @ sk_A)
% 0.21/0.50           | (r1_tarski @ (k7_relat_1 @ sk_A @ X0) @ (k7_relat_1 @ sk_B @ X0))
% 0.21/0.50           | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (r1_tarski @ (k7_relat_1 @ sk_A @ X0) @ (k7_relat_1 @ sk_B @ X0)))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))
% 0.21/0.50         | ~ (v1_relat_1 @ sk_A))) <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['2', '9'])).
% 0.21/0.50  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.21/0.50         <= (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.21/0.50       ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.21/0.50       ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('17', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf(t36_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.21/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.50  thf(t44_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.21/0.50       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.21/0.50          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf(t97_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.21/0.50          | ((k7_relat_1 @ X24 @ X25) = (X24))
% 0.21/0.50          | ~ (v1_relat_1 @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k7_relat_1 @ X0 @ (k2_xboole_0 @ X1 @ (k1_relat_1 @ X0))) = (X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf(t107_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( k7_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.21/0.50         ( k2_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         (((k7_relat_1 @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.21/0.50            = (k2_xboole_0 @ (k7_relat_1 @ X21 @ X22) @ 
% 0.21/0.50               (k7_relat_1 @ X21 @ X23)))
% 0.21/0.50          | ~ (v1_relat_1 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t107_relat_1])).
% 0.21/0.50  thf(t7_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.50  thf(t1_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.50       ( r1_tarski @ A @ C ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.50          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.50          | (r1_tarski @ X3 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k7_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X2)
% 0.21/0.50          | (r1_tarski @ (k7_relat_1 @ X2 @ X1) @ X3))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k7_relat_1 @ X0 @ X2) @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ (k7_relat_1 @ X0 @ X2) @ X1)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A))))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.21/0.50      inference('split', [status(esa)], ['3'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.50          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.50          | (r1_tarski @ X3 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((r1_tarski @ sk_A @ X0)
% 0.21/0.50           | ~ (r1_tarski @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)) @ X0)))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((~ (v1_relat_1 @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.50  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ sk_B))
% 0.21/0.50         <= (((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (~ ((r1_tarski @ sk_A @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))) | 
% 0.21/0.50       ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '14', '15', '38'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
