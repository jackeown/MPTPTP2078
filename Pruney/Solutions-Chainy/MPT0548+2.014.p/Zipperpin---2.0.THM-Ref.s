%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lfso8M8Wnx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  157 ( 171 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('2',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ( ( k7_relat_1 @ X4 @ X5 )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
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
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lfso8M8Wnx
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 11 iterations in 0.007s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.45  thf(t150_relat_1, conjecture,
% 0.21/0.45    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.21/0.45  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(cc1_relat_1, axiom,
% 0.21/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.45  thf('1', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.45  thf('2', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.45  thf(t60_relat_1, axiom,
% 0.21/0.45    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.45     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.45  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.45  thf(t97_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.45         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X4 : $i, X5 : $i]:
% 0.21/0.45         (~ (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.21/0.45          | ((k7_relat_1 @ X4 @ X5) = (X4))
% 0.21/0.45          | ~ (v1_relat_1 @ X4))),
% 0.21/0.45      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.45          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.45          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.45  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.45          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.45          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['2', '7'])).
% 0.21/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.45  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf(t148_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X2 : $i, X3 : $i]:
% 0.21/0.45         (((k2_relat_1 @ (k7_relat_1 @ X2 @ X3)) = (k9_relat_1 @ X2 @ X3))
% 0.21/0.45          | ~ (v1_relat_1 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.45          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.45  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.45          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.45          | ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.45  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.45  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
