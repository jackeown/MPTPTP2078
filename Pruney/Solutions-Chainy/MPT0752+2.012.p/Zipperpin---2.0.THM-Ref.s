%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlidRVbPFV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   39 (  45 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  127 ( 154 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v5_ordinal1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

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

thf('1',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('2',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ( v5_relat_1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','4','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('16',plain,(
    ! [X4: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['14','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qlidRVbPFV
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:11:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.50  % Solved by: fo/fo7.sh
% 0.24/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.50  % done 21 iterations in 0.012s
% 0.24/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.50  % SZS output start Refutation
% 0.24/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.50  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.24/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.50  thf(cc4_ordinal1, axiom,
% 0.24/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.24/0.50  thf('0', plain, (![X5 : $i]: ((v5_ordinal1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.24/0.50      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.24/0.50  thf(t45_ordinal1, conjecture,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.24/0.50       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.24/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.50    (~( ![A:$i]:
% 0.24/0.50        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.24/0.50          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.24/0.50    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.24/0.50  thf('1', plain,
% 0.24/0.50      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.24/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.24/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.50        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.24/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.24/0.50  thf('2', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.24/0.50  thf(fc3_funct_1, axiom,
% 0.24/0.50    (![A:$i]:
% 0.24/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.24/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.24/0.50  thf('3', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.50  thf('4', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf(t60_relat_1, axiom,
% 0.24/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.50  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.50  thf(d19_relat_1, axiom,
% 0.24/0.50    (![A:$i,B:$i]:
% 0.24/0.50     ( ( v1_relat_1 @ B ) =>
% 0.24/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.50  thf('6', plain,
% 0.24/0.50      (![X1 : $i, X2 : $i]:
% 0.24/0.50         (~ (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 0.24/0.50          | (v5_relat_1 @ X1 @ X2)
% 0.24/0.50          | ~ (v1_relat_1 @ X1))),
% 0.24/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.24/0.50  thf('7', plain,
% 0.24/0.50      (![X0 : $i]:
% 0.24/0.50         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.24/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.50          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.50  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.50  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.24/0.50  thf('10', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.24/0.50      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.24/0.50  thf('11', plain,
% 0.24/0.50      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.24/0.50      inference('demod', [status(thm)], ['1', '4', '10'])).
% 0.24/0.50  thf('12', plain,
% 0.24/0.50      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.24/0.50      inference('sup-', [status(thm)], ['0', '11'])).
% 0.24/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.50  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.50  thf('14', plain, (~ (v1_funct_1 @ k1_xboole_0)),
% 0.24/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.24/0.50  thf('15', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.24/0.50  thf('16', plain, (![X4 : $i]: (v1_funct_1 @ (k6_relat_1 @ X4))),
% 0.24/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.50  thf('17', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.24/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.50  thf('18', plain, ($false), inference('demod', [status(thm)], ['14', '17'])).
% 0.24/0.50  
% 0.24/0.50  % SZS output end Refutation
% 0.24/0.50  
% 0.24/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
