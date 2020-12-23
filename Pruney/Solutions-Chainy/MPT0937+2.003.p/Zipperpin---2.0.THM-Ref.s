%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JUdxsLTMcH

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  297 ( 355 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t2_wellord2,conjecture,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( v1_relat_2 @ ( k1_wellord2 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord2])).

thf('0',plain,(
    ~ ( v1_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ X10 )
        = X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
        = X9 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d9_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ~ ( r1_relat_2 @ X8 @ ( k3_relat_1 @ X8 ) )
      | ( v1_relat_2 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r1_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ X10 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('15',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X9 ) )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('17',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X12 ) @ ( k1_wellord2 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X11 @ X9 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_relat_2 @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ X1 ) @ ( sk_C_1 @ X0 @ X1 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X4 @ X5 ) @ ( sk_C_1 @ X4 @ X5 ) ) @ X5 )
      | ( r1_relat_2 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JUdxsLTMcH
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 27 iterations in 0.026s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.19/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.19/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.48  thf(t2_wellord2, conjecture, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t2_wellord2])).
% 0.19/0.48  thf('0', plain, (~ (v1_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d1_wellord2, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.19/0.48         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.48           ( ![C:$i,D:$i]:
% 0.19/0.48             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.19/0.48               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.19/0.48                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         (((X10) != (k1_wellord2 @ X9))
% 0.19/0.48          | ((k3_relat_1 @ X10) = (X9))
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X9 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.19/0.48          | ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.19/0.48  thf('3', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.48  thf('4', plain, (![X9 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X9)) = (X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(d9_relat_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( v1_relat_2 @ A ) <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X8 : $i]:
% 0.19/0.48         (~ (r1_relat_2 @ X8 @ (k3_relat_1 @ X8))
% 0.19/0.48          | (v1_relat_2 @ X8)
% 0.19/0.48          | ~ (v1_relat_1 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.48          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf('7', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.48          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf(d1_relat_2, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( r1_relat_2 @ A @ B ) <=>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( r2_hidden @ C @ B ) =>
% 0.19/0.48               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         ((r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.19/0.48          | (r1_relat_2 @ X5 @ X4)
% 0.19/0.48          | ~ (v1_relat_1 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.19/0.48  thf(d3_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (((X10) != (k1_wellord2 @ X9))
% 0.19/0.48          | ~ (r2_hidden @ X11 @ X9)
% 0.19/0.48          | ~ (r2_hidden @ X12 @ X9)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ X10)
% 0.19/0.48          | ~ (r1_tarski @ X11 @ X12)
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ (k1_wellord2 @ X9))
% 0.19/0.48          | ~ (r1_tarski @ X11 @ X12)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.19/0.48          | ~ (r2_hidden @ X12 @ X9)
% 0.19/0.48          | ~ (r2_hidden @ X11 @ X9))),
% 0.19/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.48  thf('16', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X11 @ X12)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X11 @ X12) @ (k1_wellord2 @ X9))
% 0.19/0.48          | ~ (r2_hidden @ X12 @ X9)
% 0.19/0.48          | ~ (r2_hidden @ X11 @ X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.48          | ~ (r2_hidden @ X0 @ X1)
% 0.19/0.48          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.19/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X1)
% 0.19/0.48          | (r1_relat_2 @ X1 @ X0)
% 0.19/0.48          | (r2_hidden @ 
% 0.19/0.48             (k4_tarski @ (sk_C_1 @ X0 @ X1) @ (sk_C_1 @ X0 @ X1)) @ 
% 0.19/0.48             (k1_wellord2 @ X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['9', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         (~ (r2_hidden @ 
% 0.19/0.48             (k4_tarski @ (sk_C_1 @ X4 @ X5) @ (sk_C_1 @ X4 @ X5)) @ X5)
% 0.19/0.48          | (r1_relat_2 @ X5 @ X4)
% 0.19/0.48          | ~ (v1_relat_1 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.48          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.48  thf('24', plain, (![X13 : $i]: (v1_relat_1 @ (k1_wellord2 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.48          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.48  thf('26', plain, (![X0 : $i]: (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.19/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.48  thf('27', plain, (![X0 : $i]: (v1_relat_2 @ (k1_wellord2 @ X0))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '26'])).
% 0.19/0.48  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
