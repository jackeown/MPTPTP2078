%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o7jUOSfoU1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:10 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  144 ( 166 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','6','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o7jUOSfoU1
% 0.15/0.36  % Computer   : n016.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:22:04 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.44  % Solved by: fo/fo7.sh
% 0.23/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.44  % done 13 iterations in 0.006s
% 0.23/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.44  % SZS output start Refutation
% 0.23/0.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.44  thf(t150_relat_1, conjecture,
% 0.23/0.44    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.44    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.23/0.44    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.23/0.44  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.23/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.44  thf(t60_relat_1, axiom,
% 0.23/0.44    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.44     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.44  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.44  thf(t95_relat_1, axiom,
% 0.23/0.44    (![A:$i,B:$i]:
% 0.23/0.44     ( ( v1_relat_1 @ B ) =>
% 0.23/0.44       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.44         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.44  thf('2', plain,
% 0.23/0.44      (![X6 : $i, X7 : $i]:
% 0.23/0.44         (~ (r1_xboole_0 @ (k1_relat_1 @ X6) @ X7)
% 0.23/0.44          | ((k7_relat_1 @ X6 @ X7) = (k1_xboole_0))
% 0.23/0.44          | ~ (v1_relat_1 @ X6))),
% 0.23/0.44      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.23/0.44  thf('3', plain,
% 0.23/0.44      (![X0 : $i]:
% 0.23/0.44         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.23/0.44          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.44          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.23/0.44      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.44  thf('4', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.23/0.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.44  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.44    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.44  thf('5', plain,
% 0.23/0.44      (![X0 : $i, X1 : $i]:
% 0.23/0.44         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.44      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.44  thf('6', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.23/0.44      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.44  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.23/0.44  thf('7', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.44      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.23/0.44  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.23/0.44  thf('8', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.44  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.44  thf('10', plain,
% 0.23/0.44      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.23/0.44      inference('demod', [status(thm)], ['3', '6', '9'])).
% 0.23/0.44  thf(t148_relat_1, axiom,
% 0.23/0.44    (![A:$i,B:$i]:
% 0.23/0.44     ( ( v1_relat_1 @ B ) =>
% 0.23/0.44       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.23/0.44  thf('11', plain,
% 0.23/0.44      (![X4 : $i, X5 : $i]:
% 0.23/0.44         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.23/0.44          | ~ (v1_relat_1 @ X4))),
% 0.23/0.44      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.44  thf('12', plain,
% 0.23/0.44      (![X0 : $i]:
% 0.23/0.44         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.23/0.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.44      inference('sup+', [status(thm)], ['10', '11'])).
% 0.23/0.44  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.44      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.44  thf('14', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.44      inference('sup+', [status(thm)], ['7', '8'])).
% 0.23/0.44  thf('15', plain,
% 0.23/0.44      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.23/0.44      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.23/0.44  thf('16', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.44      inference('demod', [status(thm)], ['0', '15'])).
% 0.23/0.44  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.23/0.44  
% 0.23/0.44  % SZS output end Refutation
% 0.23/0.44  
% 0.23/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
