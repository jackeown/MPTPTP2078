%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pc86X3v3lz

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  281 ( 330 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ( X9
       != ( k1_wellord2 @ X8 ) )
      | ( ( k3_relat_1 @ X9 )
        = X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X8 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X8 ) )
        = X8 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X8: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X8 ) )
      = X8 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d9_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ~ ( r1_relat_2 @ X7 @ ( k3_relat_1 @ X7 ) )
      | ( v1_relat_2 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d9_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r1_relat_2 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9
       != ( k1_wellord2 @ X8 ) )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X11 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('13',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X8 ) )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k1_wellord2 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X10 @ X8 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('15',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ ( k1_wellord2 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X10 @ X8 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_relat_2 @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_C @ X0 @ X1 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X3 @ X4 ) @ ( sk_C @ X3 @ X4 ) ) @ X4 )
      | ( r1_relat_2 @ X4 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('22',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 )
      | ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_relat_2 @ ( k1_wellord2 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pc86X3v3lz
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:43:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 26 iterations in 0.026s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.45  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.19/0.45  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.45  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.19/0.45  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.19/0.45  thf(t2_wellord2, conjecture, (![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]: ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t2_wellord2])).
% 0.19/0.45  thf('0', plain, (~ (v1_relat_2 @ (k1_wellord2 @ sk_A))),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d1_wellord2, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ B ) =>
% 0.19/0.45       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.19/0.45         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.45           ( ![C:$i,D:$i]:
% 0.19/0.45             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.19/0.45               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.19/0.45                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i]:
% 0.19/0.45         (((X9) != (k1_wellord2 @ X8))
% 0.19/0.45          | ((k3_relat_1 @ X9) = (X8))
% 0.19/0.45          | ~ (v1_relat_1 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.19/0.45  thf('2', plain,
% 0.19/0.45      (![X8 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ (k1_wellord2 @ X8))
% 0.19/0.45          | ((k3_relat_1 @ (k1_wellord2 @ X8)) = (X8)))),
% 0.19/0.45      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.45  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.19/0.45  thf('3', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.45  thf('4', plain, (![X8 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X8)) = (X8))),
% 0.19/0.45      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.45  thf(d9_relat_2, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ A ) =>
% 0.19/0.45       ( ( v1_relat_2 @ A ) <=> ( r1_relat_2 @ A @ ( k3_relat_1 @ A ) ) ) ))).
% 0.19/0.45  thf('5', plain,
% 0.19/0.45      (![X7 : $i]:
% 0.19/0.45         (~ (r1_relat_2 @ X7 @ (k3_relat_1 @ X7))
% 0.19/0.45          | (v1_relat_2 @ X7)
% 0.19/0.45          | ~ (v1_relat_1 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_relat_2])).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.45          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.45  thf('7', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.45  thf('8', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         (~ (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.45          | (v1_relat_2 @ (k1_wellord2 @ X0)))),
% 0.19/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.45  thf(d1_relat_2, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_relat_1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( r1_relat_2 @ A @ B ) <=>
% 0.19/0.45           ( ![C:$i]:
% 0.19/0.45             ( ( r2_hidden @ C @ B ) =>
% 0.19/0.45               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.19/0.45  thf('9', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i]:
% 0.19/0.45         ((r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.19/0.45          | (r1_relat_2 @ X4 @ X3)
% 0.19/0.45          | ~ (v1_relat_1 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.19/0.45  thf(d10_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.45  thf('10', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.45  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.45  thf('12', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.45         (((X9) != (k1_wellord2 @ X8))
% 0.19/0.45          | ~ (r2_hidden @ X10 @ X8)
% 0.19/0.45          | ~ (r2_hidden @ X11 @ X8)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.19/0.45          | ~ (r1_tarski @ X10 @ X11)
% 0.19/0.45          | ~ (v1_relat_1 @ X9))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ (k1_wellord2 @ X8))
% 0.19/0.45          | ~ (r1_tarski @ X10 @ X11)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ (k1_wellord2 @ X8))
% 0.19/0.45          | ~ (r2_hidden @ X11 @ X8)
% 0.19/0.45          | ~ (r2_hidden @ X10 @ X8))),
% 0.19/0.45      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.45  thf('14', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.45         (~ (r1_tarski @ X10 @ X11)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ (k1_wellord2 @ X8))
% 0.19/0.45          | ~ (r2_hidden @ X11 @ X8)
% 0.19/0.45          | ~ (r2_hidden @ X10 @ X8))),
% 0.19/0.45      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.45          | ~ (r2_hidden @ X0 @ X1)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['11', '15'])).
% 0.19/0.45  thf('17', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.19/0.45          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.45      inference('simplify', [status(thm)], ['16'])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]:
% 0.19/0.45         (~ (v1_relat_1 @ X1)
% 0.19/0.45          | (r1_relat_2 @ X1 @ X0)
% 0.19/0.45          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_C @ X0 @ X1)) @ 
% 0.19/0.45             (k1_wellord2 @ X0)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['9', '17'])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i]:
% 0.19/0.45         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X3 @ X4) @ (sk_C @ X3 @ X4)) @ X4)
% 0.19/0.45          | (r1_relat_2 @ X4 @ X3)
% 0.19/0.45          | ~ (v1_relat_1 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.19/0.45  thf('20', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.45          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.45          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.19/0.45          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.45  thf('21', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.45  thf('22', plain, (![X12 : $i]: (v1_relat_1 @ (k1_wellord2 @ X12))),
% 0.19/0.45      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.45  thf('23', plain,
% 0.19/0.45      (![X0 : $i]:
% 0.19/0.45         ((r1_relat_2 @ (k1_wellord2 @ X0) @ X0)
% 0.19/0.45          | (r1_relat_2 @ (k1_wellord2 @ X0) @ X0))),
% 0.19/0.45      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.45  thf('24', plain, (![X0 : $i]: (r1_relat_2 @ (k1_wellord2 @ X0) @ X0)),
% 0.19/0.45      inference('simplify', [status(thm)], ['23'])).
% 0.19/0.45  thf('25', plain, (![X0 : $i]: (v1_relat_2 @ (k1_wellord2 @ X0))),
% 0.19/0.45      inference('demod', [status(thm)], ['8', '24'])).
% 0.19/0.45  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
