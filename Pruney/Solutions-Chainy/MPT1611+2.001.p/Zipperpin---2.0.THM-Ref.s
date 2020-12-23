%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtmZ4KlDbX

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 120 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  289 ( 634 expanded)
%              Number of equality atoms :   39 (  88 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X44: $i] :
      ( ( k9_setfam_1 @ X44 )
      = ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('2',plain,(
    ! [X27: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('3',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X47 ) @ X47 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = ( k3_tarski @ X47 ) )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ( ( k3_yellow_1 @ X48 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('6',plain,(
    ! [X27: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ( X20
       != ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X44: $i] :
      ( ( k9_setfam_1 @ X44 )
      = ( k1_zfmisc_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ ( k9_setfam_1 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','14'])).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('16',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ ( k9_setfam_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( X2 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k9_setfam_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k9_setfam_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('25',plain,
    ( ( k3_tarski @ o_0_0_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k9_setfam_1 @ ( k3_tarski @ o_0_0_xboole_0 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('28',plain,(
    r2_hidden @ ( k3_tarski @ o_0_0_xboole_0 ) @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X10 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X25 )
      | ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TtmZ4KlDbX
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 105 iterations in 0.048s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(t99_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.22/0.52  thf('0', plain, (![X27 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X27)) = (X27))),
% 0.22/0.52      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.22/0.52  thf(redefinition_k9_setfam_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('1', plain, (![X44 : $i]: ((k9_setfam_1 @ X44) = (k1_zfmisc_1 @ X44))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.52  thf('2', plain, (![X27 : $i]: ((k3_tarski @ (k9_setfam_1 @ X27)) = (X27))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf(t14_yellow_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.22/0.52         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X47 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (k3_tarski @ X47) @ X47)
% 0.22/0.52          | ((k4_yellow_0 @ (k2_yellow_1 @ X47)) = (k3_tarski @ X47))
% 0.22/0.52          | (v1_xboole_0 @ X47))),
% 0.22/0.52      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.22/0.52          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.52          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.22/0.52              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t4_yellow_1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X48 : $i]: ((k3_yellow_1 @ X48) = (k2_yellow_1 @ (k9_setfam_1 @ X48)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.22/0.52  thf('6', plain, (![X27 : $i]: ((k3_tarski @ (k9_setfam_1 @ X27)) = (X27))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.22/0.52          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.52          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('9', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.22/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.52  thf(d1_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X18 @ X19)
% 0.22/0.52          | (r2_hidden @ X18 @ X20)
% 0.22/0.52          | ((X20) != (k1_zfmisc_1 @ X19)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         ((r2_hidden @ X18 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 0.22/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.52  thf('12', plain, (![X44 : $i]: ((k9_setfam_1 @ X44) = (k1_zfmisc_1 @ X44))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         ((r2_hidden @ X18 @ (k9_setfam_1 @ X19)) | ~ (r1_tarski @ X18 @ X19))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.22/0.52          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '14'])).
% 0.22/0.52  thf(t19_yellow_1, conjecture,
% 0.22/0.52    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.22/0.52  thf('16', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((sk_A) != (sk_A)) | (v1_xboole_0 @ (k9_setfam_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, ((v1_xboole_0 @ (k9_setfam_1 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.52  thf(l13_xboole_0, axiom,
% 0.22/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.22/0.52  thf('20', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X2 : $i]: (((X2) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 0.22/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, (((k9_setfam_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '21'])).
% 0.22/0.52  thf('23', plain, (((k9_setfam_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '21'])).
% 0.22/0.52  thf('24', plain, (![X27 : $i]: ((k3_tarski @ (k9_setfam_1 @ X27)) = (X27))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('25', plain, (((k3_tarski @ o_0_0_xboole_0) = (sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((k9_setfam_1 @ (k3_tarski @ o_0_0_xboole_0)) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '25'])).
% 0.22/0.52  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '13'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((r2_hidden @ (k3_tarski @ o_0_0_xboole_0) @ o_0_0_xboole_0)),
% 0.22/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf(t4_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.52  thf('30', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.52  thf('31', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X10 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X10) = (o_0_0_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.52  thf(t64_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.52       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         (((X23) != (X25))
% 0.22/0.52          | ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.52  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.22/0.52  thf('36', plain, ($false), inference('sup-', [status(thm)], ['28', '35'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
