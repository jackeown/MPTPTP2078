%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vBt1SIWbXt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 (  56 expanded)
%              Number of leaves         :   29 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  285 ( 303 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_setfam_1_type,type,(
    k2_setfam_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X12 @ X13 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t29_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ) )).

thf('4',plain,(
    ! [X25: $i] :
      ( r1_setfam_1 @ X25 @ ( k2_setfam_1 @ X25 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_setfam_1])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X23 ) @ ( k3_tarski @ X24 ) )
      | ~ ( r1_setfam_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ X0 ) @ ( k3_tarski @ ( k2_setfam_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X14 @ X16 ) @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_tarski @ X0 ) @ X1 ) @ ( k2_zfmisc_1 @ ( k3_tarski @ ( k2_setfam_1 @ X0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t139_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X18 ) @ ( k2_zfmisc_1 @ X19 @ X20 ) )
      | ( r1_tarski @ X18 @ X20 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t139_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_tarski @ X1 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_enumset1 @ X4 @ X4 @ X4 @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X27 ) @ X26 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t78_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t78_relat_1])).

thf('19',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A ) ) @ sk_A )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vBt1SIWbXt
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:38:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 32 iterations in 0.023s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.48  thf(k2_setfam_1_type, type, k2_setfam_1: $i > $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(t51_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.48       ( A ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.48           = (X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.48  thf(t77_enumset1, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         ((k2_enumset1 @ X2 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.22/0.48  thf(l51_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         ((k3_tarski @ (k2_tarski @ X12 @ X13)) = (k2_xboole_0 @ X12 @ X13))),
% 0.22/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.22/0.48           = (k2_xboole_0 @ X1 @ X0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(t29_setfam_1, axiom,
% 0.22/0.48    (![A:$i]: ( r1_setfam_1 @ A @ ( k2_setfam_1 @ A @ A ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X25 : $i]: (r1_setfam_1 @ X25 @ (k2_setfam_1 @ X25 @ X25))),
% 0.22/0.48      inference('cnf', [status(esa)], [t29_setfam_1])).
% 0.22/0.48  thf(t18_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_setfam_1 @ A @ B ) =>
% 0.22/0.48       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X23 : $i, X24 : $i]:
% 0.22/0.48         ((r1_tarski @ (k3_tarski @ X23) @ (k3_tarski @ X24))
% 0.22/0.48          | ~ (r1_setfam_1 @ X23 @ X24))),
% 0.22/0.48      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (r1_tarski @ (k3_tarski @ X0) @ (k3_tarski @ (k2_setfam_1 @ X0 @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(t118_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.48         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.48         (~ (r1_tarski @ X14 @ X15)
% 0.22/0.48          | (r1_tarski @ (k2_zfmisc_1 @ X14 @ X16) @ (k2_zfmisc_1 @ X15 @ X16)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (r1_tarski @ (k2_zfmisc_1 @ (k3_tarski @ X0) @ X1) @ 
% 0.22/0.48          (k2_zfmisc_1 @ (k3_tarski @ (k2_setfam_1 @ X0 @ X0)) @ X1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(t139_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i,C:$i,D:$i]:
% 0.22/0.48         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.22/0.48             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.22/0.48           ( r1_tarski @ B @ D ) ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k2_zfmisc_1 @ X17 @ X18) @ (k2_zfmisc_1 @ X19 @ X20))
% 0.22/0.48          | (r1_tarski @ X18 @ X20)
% 0.22/0.48          | (v1_xboole_0 @ X17))),
% 0.22/0.48      inference('cnf', [status(esa)], [t139_zfmisc_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k3_tarski @ X1)) | (r1_tarski @ X0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X2))),
% 0.22/0.48      inference('sup+', [status(thm)], ['3', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i, X2 : $i]: ((v1_xboole_0 @ X0) | (r1_tarski @ X2 @ X2))),
% 0.22/0.48      inference('sup+', [status(thm)], ['0', '11'])).
% 0.22/0.48  thf(t87_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X4 : $i]: ((k3_enumset1 @ X4 @ X4 @ X4 @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.22/0.48  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.22/0.48  thf('14', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i]: ~ (v1_xboole_0 @ (k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.22/0.48  thf(t77_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.48         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X26 : $i, X27 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.22/0.48          | ((k5_relat_1 @ (k6_relat_1 @ X27) @ X26) = (X26))
% 0.22/0.48          | ~ (v1_relat_1 @ X26))),
% 0.22/0.48      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf(t78_relat_1, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( v1_relat_1 @ A ) =>
% 0.22/0.48          ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t78_relat_1])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_A)) @ sk_A) != (sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain, (((sk_A) != (sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
