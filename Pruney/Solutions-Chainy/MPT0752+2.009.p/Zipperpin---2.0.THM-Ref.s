%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cogE11dk4D

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :  124 ( 126 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('3',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf('5',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['0','3','4'])).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('7',plain,(
    ! [X15: $i] :
      ( ( v5_ordinal1 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf('8',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X5 @ ( k1_tarski @ X4 ) )
       != X5 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['9','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cogE11dk4D
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 32 iterations in 0.016s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.48  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(t45_ordinal1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.22/0.48       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.22/0.48          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.22/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.48        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.48  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.48  thf(cc1_funct_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.22/0.48  thf('2', plain, (![X14 : $i]: ((v1_funct_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.48  thf('3', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(l222_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.22/0.48  thf('4', plain, (![X12 : $i]: (v5_relat_1 @ k1_xboole_0 @ X12)),
% 0.22/0.48      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.22/0.48  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.48  thf(cc4_ordinal1, axiom,
% 0.22/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.22/0.48  thf('7', plain, (![X15 : $i]: ((v5_ordinal1 @ X15) | ~ (v1_xboole_0 @ X15))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.22/0.48  thf('8', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('demod', [status(thm)], ['5', '8'])).
% 0.22/0.48  thf(d1_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X9 : $i]: ((v1_relat_1 @ X9) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.48  thf(t4_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.48  thf(t65_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.48          | ((k4_xboole_0 @ X5 @ (k1_tarski @ X4)) != (X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '14'])).
% 0.22/0.48  thf('16', plain, ($false), inference('demod', [status(thm)], ['9', '15'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
