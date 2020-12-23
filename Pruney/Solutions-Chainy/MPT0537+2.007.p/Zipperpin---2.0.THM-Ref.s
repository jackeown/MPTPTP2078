%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3esE81ddu0

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  77 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  315 ( 432 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X40 @ X41 ) @ ( k2_zfmisc_1 @ X42 @ X43 ) )
      | ~ ( r1_xboole_0 @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X10 ) ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k8_relat_1 @ X47 @ X46 )
        = ( k3_xboole_0 @ X46 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ X47 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('16',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k8_relat_1 @ X47 @ X46 )
        = ( k1_setfam_1 @ ( k2_tarski @ X46 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X46 ) @ X47 ) ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) )
      = ( k3_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t137_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k8_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t137_relat_1])).

thf('24',plain,(
    ( k8_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X11 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X10 ) ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('33',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3esE81ddu0
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 111 iterations in 0.077s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('0', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(t127_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.53       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ (k2_zfmisc_1 @ X40 @ X41) @ (k2_zfmisc_1 @ X42 @ X43))
% 0.21/0.53          | ~ (r1_xboole_0 @ X41 @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X0) @ 
% 0.21/0.53          (k2_zfmisc_1 @ X1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(d1_xboole_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.53  thf('4', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.53  thf(t12_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('6', plain, (![X3 : $i]: ((k1_setfam_1 @ (k2_tarski @ X3 @ X3)) = (X3))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t4_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.21/0.53          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X9 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X10)))
% 0.21/0.53          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '11'])).
% 0.21/0.53  thf(l13_xboole_0, axiom,
% 0.21/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf(t124_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k8_relat_1 @ A @ B ) =
% 0.21/0.53         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X46 : $i, X47 : $i]:
% 0.21/0.53         (((k8_relat_1 @ X47 @ X46)
% 0.21/0.53            = (k3_xboole_0 @ X46 @ (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ X47)))
% 0.21/0.53          | ~ (v1_relat_1 @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X46 : $i, X47 : $i]:
% 0.21/0.53         (((k8_relat_1 @ X47 @ X46)
% 0.21/0.53            = (k1_setfam_1 @ 
% 0.21/0.53               (k2_tarski @ X46 @ (k2_zfmisc_1 @ (k1_relat_1 @ X46) @ X47))))
% 0.21/0.53          | ~ (v1_relat_1 @ X46))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k8_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.53            = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['14', '17'])).
% 0.21/0.53  thf(t2_boole, axiom,
% 0.21/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X44 : $i, X45 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X44 @ X45)) = (k3_xboole_0 @ X44 @ X45))),
% 0.21/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k8_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['18', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.53  thf(t137_relat_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ A ) =>
% 0.21/0.53          ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t137_relat_1])).
% 0.21/0.53  thf('24', plain, (((k8_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k8_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.53        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X11 : $i]:
% 0.21/0.53         ((k1_setfam_1 @ (k2_tarski @ X11 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X9 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X10)))
% 0.21/0.53          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf('33', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['28', '33'])).
% 0.21/0.53  thf('35', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27', '34'])).
% 0.21/0.53  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
