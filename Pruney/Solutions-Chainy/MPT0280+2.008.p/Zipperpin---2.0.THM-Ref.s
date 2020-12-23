%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pjFle6X970

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:45 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  363 ( 476 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t81_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ ( k3_tarski @ X48 ) )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X51 ) @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k3_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t110_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k5_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X51 ) @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k5_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t110_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X2 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pjFle6X970
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.32/2.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.32/2.51  % Solved by: fo/fo7.sh
% 2.32/2.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.32/2.51  % done 1371 iterations in 2.064s
% 2.32/2.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.32/2.51  % SZS output start Refutation
% 2.32/2.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.32/2.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.32/2.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.32/2.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.32/2.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.32/2.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.32/2.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.32/2.51  thf(sk_B_type, type, sk_B: $i).
% 2.32/2.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.32/2.51  thf(sk_A_type, type, sk_A: $i).
% 2.32/2.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.32/2.51  thf(t81_zfmisc_1, conjecture,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( r1_tarski @
% 2.32/2.51       ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.32/2.51       ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.32/2.51  thf(zf_stmt_0, negated_conjecture,
% 2.32/2.51    (~( ![A:$i,B:$i]:
% 2.32/2.51        ( r1_tarski @
% 2.32/2.51          ( k2_xboole_0 @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) @ 
% 2.32/2.51          ( k1_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 2.32/2.51    inference('cnf.neg', [status(esa)], [t81_zfmisc_1])).
% 2.32/2.51  thf('0', plain,
% 2.32/2.51      (~ (r1_tarski @ 
% 2.32/2.51          (k2_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ (k1_zfmisc_1 @ sk_B)) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 2.32/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.32/2.51  thf(t98_xboole_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.32/2.51  thf('1', plain,
% 2.32/2.51      (![X12 : $i, X13 : $i]:
% 2.32/2.51         ((k2_xboole_0 @ X12 @ X13)
% 2.32/2.51           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 2.32/2.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.32/2.51  thf(commutativity_k3_xboole_0, axiom,
% 2.32/2.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.32/2.51  thf('2', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.32/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.32/2.51  thf(d2_tarski, axiom,
% 2.32/2.51    (![A:$i,B:$i,C:$i]:
% 2.32/2.51     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 2.32/2.51       ( ![D:$i]:
% 2.32/2.51         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 2.32/2.51  thf('3', plain,
% 2.32/2.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 2.32/2.51         (((X15) != (X14))
% 2.32/2.51          | (r2_hidden @ X15 @ X16)
% 2.32/2.51          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 2.32/2.51      inference('cnf', [status(esa)], [d2_tarski])).
% 2.32/2.51  thf('4', plain,
% 2.32/2.51      (![X14 : $i, X17 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X17 @ X14))),
% 2.32/2.51      inference('simplify', [status(thm)], ['3'])).
% 2.32/2.51  thf(l49_zfmisc_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.32/2.51  thf('5', plain,
% 2.32/2.51      (![X47 : $i, X48 : $i]:
% 2.32/2.51         ((r1_tarski @ X47 @ (k3_tarski @ X48)) | ~ (r2_hidden @ X47 @ X48))),
% 2.32/2.51      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 2.32/2.51  thf('6', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['4', '5'])).
% 2.32/2.51  thf(l51_zfmisc_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.32/2.51  thf('7', plain,
% 2.32/2.51      (![X49 : $i, X50 : $i]:
% 2.32/2.51         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 2.32/2.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.32/2.51  thf('8', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.32/2.51      inference('demod', [status(thm)], ['6', '7'])).
% 2.32/2.51  thf(t79_zfmisc_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( ( r1_tarski @ A @ B ) =>
% 2.32/2.51       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.32/2.51  thf('9', plain,
% 2.32/2.51      (![X51 : $i, X52 : $i]:
% 2.32/2.51         ((r1_tarski @ (k1_zfmisc_1 @ X51) @ (k1_zfmisc_1 @ X52))
% 2.32/2.51          | ~ (r1_tarski @ X51 @ X52))),
% 2.32/2.51      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.32/2.51  thf('10', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['8', '9'])).
% 2.32/2.51  thf(t108_xboole_1, axiom,
% 2.32/2.51    (![A:$i,B:$i,C:$i]:
% 2.32/2.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 2.32/2.51  thf('11', plain,
% 2.32/2.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.32/2.51         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ (k3_xboole_0 @ X4 @ X6) @ X5))),
% 2.32/2.51      inference('cnf', [status(esa)], [t108_xboole_1])).
% 2.32/2.51  thf('12', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         (r1_tarski @ (k3_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['10', '11'])).
% 2.32/2.51  thf('13', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X2 @ X0)))),
% 2.32/2.51      inference('sup+', [status(thm)], ['2', '12'])).
% 2.32/2.51  thf('14', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['8', '9'])).
% 2.32/2.51  thf(t110_xboole_1, axiom,
% 2.32/2.51    (![A:$i,B:$i,C:$i]:
% 2.32/2.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 2.32/2.51       ( r1_tarski @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 2.32/2.51  thf('15', plain,
% 2.32/2.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.32/2.51         (~ (r1_tarski @ X7 @ X8)
% 2.32/2.51          | ~ (r1_tarski @ X9 @ X8)
% 2.32/2.51          | (r1_tarski @ (k5_xboole_0 @ X7 @ X9) @ X8))),
% 2.32/2.51      inference('cnf', [status(esa)], [t110_xboole_1])).
% 2.32/2.51  thf('16', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.32/2.51           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.32/2.51          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.32/2.51      inference('sup-', [status(thm)], ['14', '15'])).
% 2.32/2.51  thf('17', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         (r1_tarski @ 
% 2.32/2.51          (k5_xboole_0 @ (k1_zfmisc_1 @ X0) @ 
% 2.32/2.51           (k3_xboole_0 @ X2 @ (k1_zfmisc_1 @ X0))) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['13', '16'])).
% 2.32/2.51  thf('18', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.32/2.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.32/2.51  thf(t100_xboole_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]:
% 2.32/2.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.32/2.51  thf('19', plain,
% 2.32/2.51      (![X2 : $i, X3 : $i]:
% 2.32/2.51         ((k4_xboole_0 @ X2 @ X3)
% 2.32/2.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 2.32/2.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.32/2.51  thf('20', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         ((k4_xboole_0 @ X0 @ X1)
% 2.32/2.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup+', [status(thm)], ['18', '19'])).
% 2.32/2.51  thf('21', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         (r1_tarski @ (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('demod', [status(thm)], ['17', '20'])).
% 2.32/2.51  thf(t7_xboole_1, axiom,
% 2.32/2.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.32/2.51  thf('22', plain,
% 2.32/2.51      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 2.32/2.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.32/2.51  thf('23', plain,
% 2.32/2.51      (![X51 : $i, X52 : $i]:
% 2.32/2.51         ((r1_tarski @ (k1_zfmisc_1 @ X51) @ (k1_zfmisc_1 @ X52))
% 2.32/2.51          | ~ (r1_tarski @ X51 @ X52))),
% 2.32/2.51      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 2.32/2.51  thf('24', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['22', '23'])).
% 2.32/2.51  thf('25', plain,
% 2.32/2.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.32/2.51         (~ (r1_tarski @ X7 @ X8)
% 2.32/2.51          | ~ (r1_tarski @ X9 @ X8)
% 2.32/2.51          | (r1_tarski @ (k5_xboole_0 @ X7 @ X9) @ X8))),
% 2.32/2.51      inference('cnf', [status(esa)], [t110_xboole_1])).
% 2.32/2.51  thf('26', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         ((r1_tarski @ (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 2.32/2.51           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.32/2.51          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 2.32/2.51      inference('sup-', [status(thm)], ['24', '25'])).
% 2.32/2.51  thf('27', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.32/2.51         (r1_tarski @ 
% 2.32/2.51          (k5_xboole_0 @ (k1_zfmisc_1 @ X1) @ 
% 2.32/2.51           (k4_xboole_0 @ (k1_zfmisc_1 @ X0) @ X2)) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup-', [status(thm)], ['21', '26'])).
% 2.32/2.51  thf('28', plain,
% 2.32/2.51      (![X0 : $i, X1 : $i]:
% 2.32/2.51         (r1_tarski @ 
% 2.32/2.51          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 2.32/2.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.32/2.51      inference('sup+', [status(thm)], ['1', '27'])).
% 2.32/2.51  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 2.32/2.51  
% 2.32/2.51  % SZS output end Refutation
% 2.32/2.51  
% 2.32/2.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
