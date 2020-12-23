%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.viGIVSZ9Xj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:14 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   28 (  36 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  114 ( 250 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t46_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
       => ( ( v1_relat_1 @ A )
          & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) )
          & ( v1_funct_1 @ A )
          & ( v5_ordinal1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) )
         => ( ( v1_relat_1 @ A )
            & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) )
            & ( v1_funct_1 @ A )
            & ( v5_ordinal1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_ordinal1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v5_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_ordinal1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ A )
    <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( v5_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_ordinal1])).

thf('9',plain,(
    v5_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','9'])).

thf('11',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.viGIVSZ9Xj
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:08:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 18 iterations in 0.012s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.45  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.18/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.45  thf(d10_xboole_0, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.18/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.45  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.18/0.45      inference('simplify', [status(thm)], ['0'])).
% 0.18/0.45  thf(d19_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) =>
% 0.18/0.45       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X3 : $i, X4 : $i]:
% 0.18/0.45         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.18/0.45          | (v5_relat_1 @ X3 @ X4)
% 0.18/0.45          | ~ (v1_relat_1 @ X3))),
% 0.18/0.45      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.18/0.45  thf('3', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.18/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.45  thf(t46_ordinal1, conjecture,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.18/0.45       ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.18/0.45         ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.18/0.45           ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i]:
% 0.18/0.45        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.18/0.45          ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.18/0.45            ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.18/0.45              ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t46_ordinal1])).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      ((~ (v1_relat_1 @ sk_A)
% 0.18/0.45        | ~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))
% 0.18/0.45        | ~ (v1_funct_1 @ sk_A)
% 0.18/0.45        | ~ (v5_ordinal1 @ sk_A))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('5', plain, ((v1_relat_1 @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('6', plain, ((v1_funct_1 @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('7', plain, ((v3_ordinal1 @ (k1_relat_1 @ sk_A))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(d7_ordinal1, axiom,
% 0.18/0.45    (![A:$i]: ( ( v5_ordinal1 @ A ) <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ))).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X6 : $i]: ((v5_ordinal1 @ X6) | ~ (v3_ordinal1 @ (k1_relat_1 @ X6)))),
% 0.18/0.45      inference('cnf', [status(esa)], [d7_ordinal1])).
% 0.18/0.45  thf('9', plain, ((v5_ordinal1 @ sk_A)),
% 0.18/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.18/0.45  thf('10', plain, (~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))),
% 0.18/0.45      inference('demod', [status(thm)], ['4', '5', '6', '9'])).
% 0.18/0.45  thf('11', plain, (~ (v1_relat_1 @ sk_A)),
% 0.18/0.45      inference('sup-', [status(thm)], ['3', '10'])).
% 0.18/0.45  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('13', plain, ($false), inference('demod', [status(thm)], ['11', '12'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
