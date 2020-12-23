%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qPnOISiiEj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  205 ( 271 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t187_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
           => ( ( k7_relat_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t187_relat_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k9_relat_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k9_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k9_relat_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k7_relat_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ( k7_relat_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qPnOISiiEj
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 14 iterations in 0.011s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(t187_relat_1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.45           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ A ) =>
% 0.20/0.45          ( ![B:$i]:
% 0.20/0.45            ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.45              ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t187_relat_1])).
% 0.20/0.45  thf('0', plain, ((r1_xboole_0 @ sk_B @ (k1_relat_1 @ sk_A))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.45  thf('2', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ sk_B)),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t151_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X6 : $i, X7 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.45          | ((k9_relat_1 @ X6 @ X7) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_A) | ((k9_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('6', plain, (((k9_relat_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.45  thf(dt_k7_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X2) | (v1_relat_1 @ (k7_relat_1 @ X2 @ X3)))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.45  thf(t148_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i]:
% 0.20/0.45         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.45          | ~ (v1_relat_1 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.45  thf(t64_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.45           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.45         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X8 : $i]:
% 0.20/0.45         (((k2_relat_1 @ X8) != (k1_xboole_0))
% 0.20/0.45          | ((X8) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.45          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.46          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X1))),
% 0.20/0.46      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.46        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '12'])).
% 0.20/0.46  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46        | ((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, (((k7_relat_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.46  thf('17', plain, (((k7_relat_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('18', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
