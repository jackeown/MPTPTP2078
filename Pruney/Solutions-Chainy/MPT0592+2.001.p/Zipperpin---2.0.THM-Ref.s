%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddBht9Md6G

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  115 ( 249 expanded)
%              Number of equality atoms :   15 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t196_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k1_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k1_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( ( k1_relat_1 @ A )
                  = k1_xboole_0 )
                & ( ( k1_relat_1 @ B )
                  = k1_xboole_0 ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t196_relat_1])).

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,
    ( ( k1_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','14'])).

thf('16',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['5','15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddBht9Md6G
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 15 iterations in 0.011s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(t196_relat_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( v1_relat_1 @ B ) =>
% 0.19/0.46           ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.19/0.46               ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( v1_relat_1 @ A ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( v1_relat_1 @ B ) =>
% 0.19/0.46              ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.19/0.46                  ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t196_relat_1])).
% 0.19/0.46  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(fc8_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.46       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X2 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ (k1_relat_1 @ X2))
% 0.19/0.46          | ~ (v1_relat_1 @ X2)
% 0.19/0.46          | (v1_xboole_0 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.46        | (v1_xboole_0 @ sk_B)
% 0.19/0.46        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.46  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.46  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((v1_xboole_0 @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.19/0.46  thf(l13_xboole_0, axiom,
% 0.19/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.46  thf('7', plain, (((k1_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X2 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ (k1_relat_1 @ X2))
% 0.19/0.46          | ~ (v1_relat_1 @ X2)
% 0.19/0.46          | (v1_xboole_0 @ X2))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.46        | (v1_xboole_0 @ sk_A)
% 0.19/0.46        | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.46  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.46  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain, (![X0 : $i]: (((X0) = (sk_A)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['6', '14'])).
% 0.19/0.46  thf('16', plain, (((sk_B) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '15'])).
% 0.19/0.46  thf('17', plain, (((sk_A) != (sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('18', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
