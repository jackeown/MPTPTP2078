%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uAXdJ1QbAi

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  253 ( 333 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) @ X42 )
        = ( k7_relat_1 @ X40 @ ( k3_xboole_0 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X40 @ X41 ) @ X42 )
        = ( k7_relat_1 @ X40 @ ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t207_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_xboole_0 @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t207_relat_1])).

thf('8',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C_1 @ sk_A ) @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k7_relat_1 @ sk_C_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k7_relat_1 @ sk_C_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['15','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uAXdJ1QbAi
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 48 iterations in 0.058s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(fc16_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.20/0.52       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.20/0.52         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X38 : $i, X39 : $i]:
% 0.20/0.52         (~ (v1_relat_1 @ X38)
% 0.20/0.52          | ~ (v1_xboole_0 @ X39)
% 0.20/0.52          | (v1_xboole_0 @ (k7_relat_1 @ X38 @ X39)))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.20/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.52  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.52  thf(t8_boole, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t8_boole])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ X0)
% 0.20/0.52          | ~ (v1_relat_1 @ X1)
% 0.20/0.52          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.52  thf(t100_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.52         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.52         (((k7_relat_1 @ (k7_relat_1 @ X40 @ X41) @ X42)
% 0.20/0.52            = (k7_relat_1 @ X40 @ (k3_xboole_0 @ X41 @ X42)))
% 0.20/0.52          | ~ (v1_relat_1 @ X40))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.20/0.52  thf(t12_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X36 : $i, X37 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.20/0.52         (((k7_relat_1 @ (k7_relat_1 @ X40 @ X41) @ X42)
% 0.20/0.52            = (k7_relat_1 @ X40 @ (k1_setfam_1 @ (k2_tarski @ X41 @ X42))))
% 0.20/0.52          | ~ (v1_relat_1 @ X40))),
% 0.20/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf(t207_relat_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.52         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.52        ( ( v1_relat_1 @ C ) =>
% 0.20/0.52          ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.52            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t207_relat_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (((k7_relat_1 @ (k7_relat_1 @ sk_C_1 @ sk_A) @ sk_B_1) != (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((((k7_relat_1 @ sk_C_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1)))
% 0.20/0.52          != (k1_xboole_0))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.52  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (((k7_relat_1 @ sk_C_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1)))
% 0.20/0.52         != (k1_xboole_0))),
% 0.20/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.52        | ~ (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.52  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.52        | ~ (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1))))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (~ (v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.52  thf('16', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.52  thf(t4_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.20/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X36 : $i, X37 : $i]:
% 0.20/0.52         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.20/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.20/0.52          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      ((v1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.52  thf('23', plain, ($false), inference('demod', [status(thm)], ['15', '22'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
