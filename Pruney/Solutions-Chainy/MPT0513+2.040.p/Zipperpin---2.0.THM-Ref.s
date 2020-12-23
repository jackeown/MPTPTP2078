%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApG5omWUrr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:30 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :  165 ( 165 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X4 )
        = X4 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','7','13'])).

thf('15',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ApG5omWUrr
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 15 iterations in 0.011s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(t111_relat_1, conjecture,
% 0.19/0.46    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.19/0.46  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t60_relat_1, axiom,
% 0.19/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.46  thf(t97_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.46         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.19/0.46          | ((k7_relat_1 @ X13 @ X14) = (X13))
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.46          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t4_boole, axiom,
% 0.19/0.46    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X3 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.46  thf(l32_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.46  thf(d1_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.46              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X10 : $i]: ((v1_relat_1 @ X10) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.46  thf(l22_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ B ) =>
% 0.19/0.46       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i]:
% 0.19/0.46         (((k2_xboole_0 @ (k1_tarski @ X5) @ X4) = (X4))
% 0.19/0.46          | ~ (r2_hidden @ X5 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((v1_relat_1 @ X0)
% 0.19/0.46          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf(t49_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.19/0.46  thf('12', plain, (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_relat_1 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '7', '13'])).
% 0.19/0.46  thf('15', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '14'])).
% 0.19/0.46  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
