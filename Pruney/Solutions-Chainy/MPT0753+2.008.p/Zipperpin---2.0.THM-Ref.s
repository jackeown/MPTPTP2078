%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PRM1qKzwFQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  154 ( 290 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( v5_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v5_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_ordinal1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ A )
    <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( v5_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_ordinal1])).

thf('12',plain,(
    v5_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v5_relat_1 @ sk_A @ ( k2_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','12'])).

thf('14',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PRM1qKzwFQ
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 19 iterations in 0.013s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(t98_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X2 : $i]:
% 0.19/0.46         (((k7_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.19/0.46  thf(t99_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( r1_tarski @
% 0.19/0.46         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) @ 
% 0.19/0.46           (k2_relat_1 @ X3))
% 0.19/0.46          | ~ (v1_relat_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.46  thf(d19_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.19/0.46          | (v5_relat_1 @ X0 @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v5_relat_1 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.46  thf(t46_ordinal1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46       ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.46         ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.19/0.46           ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46          ( ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.46            ( ( v1_relat_1 @ A ) & ( v5_relat_1 @ A @ ( k2_relat_1 @ A ) ) & 
% 0.19/0.46              ( v1_funct_1 @ A ) & ( v5_ordinal1 @ A ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t46_ordinal1])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.46        | ~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))
% 0.19/0.46        | ~ (v1_funct_1 @ sk_A)
% 0.19/0.46        | ~ (v5_ordinal1 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain, ((v3_ordinal1 @ (k1_relat_1 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d7_ordinal1, axiom,
% 0.19/0.46    (![A:$i]: ( ( v5_ordinal1 @ A ) <=> ( v3_ordinal1 @ ( k1_relat_1 @ A ) ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X6 : $i]: ((v5_ordinal1 @ X6) | ~ (v3_ordinal1 @ (k1_relat_1 @ X6)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d7_ordinal1])).
% 0.19/0.46  thf('12', plain, ((v5_ordinal1 @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain, (~ (v5_relat_1 @ sk_A @ (k2_relat_1 @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8', '9', '12'])).
% 0.19/0.46  thf('14', plain, (~ (v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '13'])).
% 0.19/0.46  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
