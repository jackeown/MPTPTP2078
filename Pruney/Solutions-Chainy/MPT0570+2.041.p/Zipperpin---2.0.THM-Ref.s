%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S6QFFbkZ5P

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:13 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 239 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( k10_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k10_relat_1 @ X6 @ X7 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['5','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S6QFFbkZ5P
% 0.13/0.32  % Computer   : n001.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:30:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 22 iterations in 0.016s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.18/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.18/0.45  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.45  thf(t8_boole, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X4 : $i, X5 : $i]:
% 0.18/0.45         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t8_boole])).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.18/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.45  thf(t174_relat_1, conjecture,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) =>
% 0.18/0.45       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.45            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.18/0.45            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i,B:$i]:
% 0.18/0.45        ( ( v1_relat_1 @ B ) =>
% 0.18/0.45          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.18/0.45               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.18/0.45               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.18/0.45  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('4', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.18/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.45  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.18/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.18/0.45  thf('6', plain, (((k10_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t173_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) =>
% 0.18/0.45       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.45         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      (![X6 : $i, X7 : $i]:
% 0.18/0.45         (((k10_relat_1 @ X6 @ X7) != (k1_xboole_0))
% 0.18/0.45          | (r1_xboole_0 @ (k2_relat_1 @ X6) @ X7)
% 0.18/0.45          | ~ (v1_relat_1 @ X6))),
% 0.18/0.45      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.45        | ~ (v1_relat_1 @ sk_B)
% 0.18/0.45        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.18/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.45  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('10', plain,
% 0.18/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.45        | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.18/0.45  thf('11', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.18/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.18/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.18/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.18/0.45  thf('12', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.18/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.18/0.45  thf('13', plain, ((r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.18/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.18/0.45  thf(t69_xboole_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.45       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.18/0.45  thf('14', plain,
% 0.18/0.45      (![X2 : $i, X3 : $i]:
% 0.18/0.45         (~ (r1_xboole_0 @ X2 @ X3)
% 0.18/0.45          | ~ (r1_tarski @ X2 @ X3)
% 0.18/0.45          | (v1_xboole_0 @ X2))),
% 0.18/0.45      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.18/0.45  thf('15', plain,
% 0.18/0.45      (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.18/0.45  thf('16', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('17', plain, ((v1_xboole_0 @ sk_A)),
% 0.18/0.45      inference('demod', [status(thm)], ['15', '16'])).
% 0.18/0.45  thf('18', plain, ($false), inference('demod', [status(thm)], ['5', '17'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
