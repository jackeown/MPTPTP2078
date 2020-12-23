%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dBAsgdG6DW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 227 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t217_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v4_relat_1 @ C @ A ) )
           => ( v4_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t217_relat_1])).

thf('0',plain,(
    ~ ( v4_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dBAsgdG6DW
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 13 iterations in 0.009s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(t217_relat_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46       ( ![C:$i]:
% 0.21/0.46         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.21/0.46           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46          ( ![C:$i]:
% 0.21/0.46            ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.21/0.46              ( v4_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t217_relat_1])).
% 0.21/0.46  thf('0', plain, (~ (v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('2', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d18_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         (~ (v4_relat_1 @ X5 @ X6)
% 0.21/0.46          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.21/0.46          | ~ (v1_relat_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf(t12_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.46  thf('8', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(t11_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (r1_tarski @ sk_A @ X0) | (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]:
% 0.21/0.46         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.21/0.46          | (v4_relat_1 @ X5 @ X6)
% 0.21/0.46          | ~ (v1_relat_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.46  thf('13', plain, ((~ (v1_relat_1 @ sk_C) | (v4_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.46  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
