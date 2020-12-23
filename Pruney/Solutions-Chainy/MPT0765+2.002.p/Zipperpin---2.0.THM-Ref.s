%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f3l2Nkl4W8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  84 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 ( 992 expanded)
%              Number of equality atoms :   23 (  52 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) )
      <=> ( v2_wellord1 @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( r2_wellord1 @ X3 @ ( k3_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf(t9_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_wellord1 @ B @ A )
       => ! [C: $i] :
            ~ ( ( r1_tarski @ C @ A )
              & ( C != k1_xboole_0 )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ C )
                    & ! [E: $i] :
                        ( ( r2_hidden @ E @ C )
                       => ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 ) @ X7 )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_relat_1 @ X0 ) @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t11_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ~ ( ( v2_wellord1 @ A )
          & ( ( k3_relat_1 @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ! [C: $i] :
                    ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                   => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ~ ( ( v2_wellord1 @ A )
            & ( ( k3_relat_1 @ A )
             != k1_xboole_0 )
            & ! [B: $i] :
                ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                  & ! [C: $i] :
                      ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                     => ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord1])).

thf('8',plain,(
    ! [X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X8 ) @ ( k3_relat_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('16',plain,(
    ! [X3: $i] :
      ( ~ ( v2_wellord1 @ X3 )
      | ( r2_wellord1 @ X3 @ ( k3_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord1])).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_wellord1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X4 ) @ X6 ) @ X4 )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_wellord1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ X2 ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_wellord1 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k3_relat_1 @ X0 ) @ X0 ) @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A )
    | ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( sk_C @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_C @ X8 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k3_relat_1 @ sk_A ) @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v2_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','28'])).

thf('30',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k3_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ( k3_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f3l2Nkl4W8
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 24 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.22/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.47  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.22/0.47  thf(d10_xboole_0, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.47  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.47  thf(t8_wellord1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( r2_wellord1 @ A @ ( k3_relat_1 @ A ) ) <=> ( v2_wellord1 @ A ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v2_wellord1 @ X3)
% 0.22/0.47          | (r2_wellord1 @ X3 @ (k3_relat_1 @ X3))
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.22/0.47  thf(t9_wellord1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( r2_wellord1 @ B @ A ) =>
% 0.22/0.47         ( ![C:$i]:
% 0.22/0.47           ( ~( ( r1_tarski @ C @ A ) & ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47                ( ![D:$i]:
% 0.22/0.47                  ( ~( ( r2_hidden @ D @ C ) & 
% 0.22/0.47                       ( ![E:$i]:
% 0.22/0.47                         ( ( r2_hidden @ E @ C ) =>
% 0.22/0.47                           ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.22/0.47         (~ (r2_wellord1 @ X4 @ X5)
% 0.22/0.47          | (r2_hidden @ (sk_D @ X7 @ X4) @ X7)
% 0.22/0.47          | ((X7) = (k1_xboole_0))
% 0.22/0.47          | ~ (r1_tarski @ X7 @ X5)
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t9_wellord1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.47          | ((X1) = (k1_xboole_0))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X1 @ X0) @ X1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r2_hidden @ (sk_D @ X1 @ X0) @ X1)
% 0.22/0.47          | ((X1) = (k1_xboole_0))
% 0.22/0.47          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | (r2_hidden @ (sk_D @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | (r2_hidden @ (sk_D @ (k3_relat_1 @ X0) @ X0) @ (k3_relat_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.22/0.47  thf(t11_wellord1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ~( ( v2_wellord1 @ A ) & ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47            ( ![B:$i]:
% 0.22/0.47              ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.22/0.47                   ( ![C:$i]:
% 0.22/0.47                     ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.22/0.47                       ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ A ) =>
% 0.22/0.47          ( ~( ( v2_wellord1 @ A ) & 
% 0.22/0.47               ( ( k3_relat_1 @ A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.47               ( ![B:$i]:
% 0.22/0.47                 ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.22/0.47                      ( ![C:$i]:
% 0.22/0.47                        ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) =>
% 0.22/0.47                          ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t11_wellord1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X8 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X8 @ (k3_relat_1 @ sk_A))
% 0.22/0.47          | (r2_hidden @ (sk_C @ X8) @ (k3_relat_1 @ sk_A)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.47        | ~ (v2_wellord1 @ sk_A)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_A)
% 0.22/0.47        | (r2_hidden @ (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.22/0.47           (k3_relat_1 @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain, ((v2_wellord1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.47        | (r2_hidden @ (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.22/0.47           (k3_relat_1 @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.47  thf('13', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((r2_hidden @ (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A)) @ 
% 0.22/0.47        (k3_relat_1 @ sk_A))),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X3 : $i]:
% 0.22/0.47         (~ (v2_wellord1 @ X3)
% 0.22/0.47          | (r2_wellord1 @ X3 @ (k3_relat_1 @ X3))
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t8_wellord1])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.47         (~ (r2_wellord1 @ X4 @ X5)
% 0.22/0.47          | ~ (r2_hidden @ X6 @ X7)
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X4) @ X6) @ X4)
% 0.22/0.47          | ((X7) = (k1_xboole_0))
% 0.22/0.47          | ~ (r1_tarski @ X7 @ X5)
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t9_wellord1])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.47          | ((X1) = (k1_xboole_0))
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 0.22/0.47          | ~ (r2_hidden @ X2 @ X1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X2 @ X1)
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X1 @ X0) @ X2) @ X0)
% 0.22/0.47          | ((X1) = (k1_xboole_0))
% 0.22/0.47          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0))
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v2_wellord1 @ X0)
% 0.22/0.47          | ((k3_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ (k3_relat_1 @ X0) @ X0) @ X1) @ 
% 0.22/0.47             X0)
% 0.22/0.47          | ~ (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['15', '19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (((r2_hidden @ 
% 0.22/0.47         (k4_tarski @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.22/0.47          (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.22/0.47         sk_A)
% 0.22/0.47        | ((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.47        | ~ (v2_wellord1 @ sk_A)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '20'])).
% 0.22/0.47  thf('22', plain, ((v2_wellord1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (((r2_hidden @ 
% 0.22/0.47         (k4_tarski @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.22/0.47          (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.22/0.47         sk_A)
% 0.22/0.47        | ((k3_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.47      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.22/0.47  thf('25', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      ((r2_hidden @ 
% 0.22/0.47        (k4_tarski @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A) @ 
% 0.22/0.47         (sk_C @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A))) @ 
% 0.22/0.47        sk_A)),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      (![X8 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X8 @ (k3_relat_1 @ sk_A))
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X8 @ (sk_C @ X8)) @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (~ (r2_hidden @ (sk_D @ (k3_relat_1 @ sk_A) @ sk_A) @ (k3_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      ((((k3_relat_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.47        | ~ (v2_wellord1 @ sk_A)
% 0.22/0.47        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '28'])).
% 0.22/0.47  thf('30', plain, ((v2_wellord1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('32', plain, (((k3_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.47  thf('33', plain, (((k3_relat_1 @ sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('34', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
