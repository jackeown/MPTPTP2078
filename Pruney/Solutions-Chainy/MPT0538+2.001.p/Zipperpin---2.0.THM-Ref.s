%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pssaoV3ko6

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 245 expanded)
%              Number of equality atoms :   34 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t138_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k8_relat_1 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k8_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t138_relat_1])).

thf('0',plain,(
    ( k8_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ( k8_relat_1 @ sk_A @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k3_xboole_0 @ X36 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X36 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ o_0_0_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ o_0_0_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X4 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ o_0_0_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k8_relat_1 @ X0 @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( o_0_0_xboole_0
        = ( k8_relat_1 @ X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k8_relat_1 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pssaoV3ko6
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 28 iterations in 0.014s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(t138_relat_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.21/0.46  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.46  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('3', plain, (((k8_relat_1 @ sk_A @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.21/0.46  thf(cc1_relat_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.46  thf('4', plain, (![X35 : $i]: ((v1_relat_1 @ X35) | ~ (v1_xboole_0 @ X35))),
% 0.21/0.46      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.46  thf(t124_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( k8_relat_1 @ A @ B ) =
% 0.21/0.46         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X36 : $i, X37 : $i]:
% 0.21/0.46         (((k8_relat_1 @ X37 @ X36)
% 0.21/0.46            = (k3_xboole_0 @ X36 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 0.21/0.46          | ~ (v1_relat_1 @ X36))),
% 0.21/0.46      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.21/0.46  thf(t12_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X33 : $i, X34 : $i]:
% 0.21/0.46         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X36 : $i, X37 : $i]:
% 0.21/0.46         (((k8_relat_1 @ X37 @ X36)
% 0.21/0.46            = (k1_setfam_1 @ 
% 0.21/0.46               (k2_tarski @ X36 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37))))
% 0.21/0.46          | ~ (v1_relat_1 @ X36))),
% 0.21/0.46      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.46  thf(t5_boole, axiom,
% 0.21/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.46  thf('9', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.46  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('11', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ o_0_0_xboole_0) = (X5))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, (![X0 : $i]: ((k5_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['8', '11'])).
% 0.21/0.46  thf(t100_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.46           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X33 : $i, X34 : $i]:
% 0.21/0.46         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.21/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.46           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k4_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.21/0.46           = (k1_setfam_1 @ (k2_tarski @ o_0_0_xboole_0 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf(t4_boole, axiom,
% 0.21/0.46    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.46  thf('18', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('19', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X4 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X4) = (o_0_0_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((o_0_0_xboole_0) = (k1_setfam_1 @ (k2_tarski @ o_0_0_xboole_0 @ X0)))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '20'])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((o_0_0_xboole_0) = (k8_relat_1 @ X0 @ o_0_0_xboole_0))
% 0.21/0.46          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['7', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.21/0.46          | ((o_0_0_xboole_0) = (k8_relat_1 @ X0 @ o_0_0_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['4', '22'])).
% 0.21/0.46  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.21/0.46  thf('24', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.46  thf('25', plain,
% 0.21/0.46      (![X0 : $i]: ((o_0_0_xboole_0) = (k8_relat_1 @ X0 @ o_0_0_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.46  thf('26', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['3', '25'])).
% 0.21/0.46  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
