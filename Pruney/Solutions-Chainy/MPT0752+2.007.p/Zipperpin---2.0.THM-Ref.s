%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxE9rya2Qf

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:13 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :  124 ( 126 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X12: $i] :
      ( ( v1_funct_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('3',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X10 ) ),
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
    ! [X13: $i] :
      ( ( v5_ordinal1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
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
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['9','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yxE9rya2Qf
% 0.16/0.37  % Computer   : n008.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 14:42:30 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.25/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.50  % Solved by: fo/fo7.sh
% 0.25/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.50  % done 25 iterations in 0.013s
% 0.25/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.50  % SZS output start Refutation
% 0.25/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.50  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.25/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.25/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.25/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.25/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.50  thf(t45_ordinal1, conjecture,
% 0.25/0.50    (![A:$i]:
% 0.25/0.50     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.25/0.50       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.25/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.50    (~( ![A:$i]:
% 0.25/0.50        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.25/0.50          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.25/0.50    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.25/0.50  thf('0', plain,
% 0.25/0.50      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.25/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.25/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.25/0.50        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.25/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.25/0.50  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.50  thf(cc1_funct_1, axiom,
% 0.25/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.25/0.50  thf('2', plain, (![X12 : $i]: ((v1_funct_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.25/0.50      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.25/0.50  thf('3', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.25/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.50  thf(l222_relat_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.25/0.50  thf('4', plain, (![X10 : $i]: (v5_relat_1 @ k1_xboole_0 @ X10)),
% 0.25/0.50      inference('cnf', [status(esa)], [l222_relat_1])).
% 0.25/0.50  thf('5', plain,
% 0.25/0.50      ((~ (v5_ordinal1 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.25/0.50      inference('demod', [status(thm)], ['0', '3', '4'])).
% 0.25/0.50  thf('6', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.25/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.25/0.50  thf(cc4_ordinal1, axiom,
% 0.25/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.25/0.50  thf('7', plain, (![X13 : $i]: ((v5_ordinal1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.25/0.50      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.25/0.50  thf('8', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.25/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.25/0.50  thf('9', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.25/0.50      inference('demod', [status(thm)], ['5', '8'])).
% 0.25/0.50  thf(d1_relat_1, axiom,
% 0.25/0.50    (![A:$i]:
% 0.25/0.50     ( ( v1_relat_1 @ A ) <=>
% 0.25/0.50       ( ![B:$i]:
% 0.25/0.50         ( ~( ( r2_hidden @ B @ A ) & 
% 0.25/0.50              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.25/0.50  thf('10', plain,
% 0.25/0.50      (![X7 : $i]: ((v1_relat_1 @ X7) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.25/0.50      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.25/0.50  thf(t113_zfmisc_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]:
% 0.25/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.25/0.50  thf('11', plain,
% 0.25/0.50      (![X1 : $i, X2 : $i]:
% 0.25/0.50         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.25/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.50  thf('12', plain,
% 0.25/0.50      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.25/0.50  thf(t152_zfmisc_1, axiom,
% 0.25/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.25/0.50  thf('13', plain,
% 0.25/0.50      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.25/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.25/0.50  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.25/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.25/0.50  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.25/0.50      inference('sup-', [status(thm)], ['10', '14'])).
% 0.25/0.50  thf('16', plain, ($false), inference('demod', [status(thm)], ['9', '15'])).
% 0.25/0.50  
% 0.25/0.50  % SZS output end Refutation
% 0.25/0.50  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
