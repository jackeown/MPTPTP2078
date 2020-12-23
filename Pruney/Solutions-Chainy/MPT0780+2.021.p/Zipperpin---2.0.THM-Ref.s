%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9GWQMXtZoL

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:28 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :  401 ( 504 expanded)
%              Number of equality atoms :   37 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X52 @ X54 ) @ X53 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X52 @ X53 ) @ X54 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X49 @ X50 ) @ X51 )
        = ( k2_wellord1 @ X49 @ ( k3_xboole_0 @ X50 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X49 @ X50 ) @ X51 )
        = ( k2_wellord1 @ X49 @ ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X2 @ X1 ) @ X0 )
        = ( k2_wellord1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('6',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_wellord1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( ( k7_relat_1 @ X41 @ X42 )
        = X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) )
        = ( k9_relat_1 @ X33 @ X34 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ ( k6_relat_1 @ X43 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X44 ) @ ( k6_relat_1 @ X43 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) )
        = ( k9_relat_1 @ X35 @ ( k2_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X38: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25','26'])).

thf('28',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9GWQMXtZoL
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 524 iterations in 0.350s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.62/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.62/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.62/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.80  thf(t27_wellord1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ C ) =>
% 0.62/0.80       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.62/0.80         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.62/0.80  thf('0', plain,
% 0.62/0.80      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.62/0.80         (((k2_wellord1 @ (k2_wellord1 @ X52 @ X54) @ X53)
% 0.62/0.80            = (k2_wellord1 @ (k2_wellord1 @ X52 @ X53) @ X54))
% 0.62/0.80          | ~ (v1_relat_1 @ X52))),
% 0.62/0.80      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.62/0.80  thf(t26_wellord1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ C ) =>
% 0.62/0.80       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.62/0.80         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.62/0.80         (((k2_wellord1 @ (k2_wellord1 @ X49 @ X50) @ X51)
% 0.62/0.80            = (k2_wellord1 @ X49 @ (k3_xboole_0 @ X50 @ X51)))
% 0.62/0.80          | ~ (v1_relat_1 @ X49))),
% 0.62/0.80      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.62/0.80  thf(t12_setfam_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.62/0.80  thf('2', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.62/0.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.62/0.80         (((k2_wellord1 @ (k2_wellord1 @ X49 @ X50) @ X51)
% 0.62/0.80            = (k2_wellord1 @ X49 @ (k1_setfam_1 @ (k2_tarski @ X50 @ X51))))
% 0.62/0.80          | ~ (v1_relat_1 @ X49))),
% 0.62/0.80      inference('demod', [status(thm)], ['1', '2'])).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.62/0.80            = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 0.62/0.80          | ~ (v1_relat_1 @ X2)
% 0.62/0.80          | ~ (v1_relat_1 @ X2))),
% 0.62/0.80      inference('sup+', [status(thm)], ['0', '3'])).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X2)
% 0.62/0.80          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.62/0.80              = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 0.62/0.80      inference('simplify', [status(thm)], ['4'])).
% 0.62/0.80  thf(t29_wellord1, conjecture,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ C ) =>
% 0.62/0.80       ( ( r1_tarski @ A @ B ) =>
% 0.62/0.80         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.62/0.80           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.80        ( ( v1_relat_1 @ C ) =>
% 0.62/0.80          ( ( r1_tarski @ A @ B ) =>
% 0.62/0.80            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.62/0.80              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.62/0.80  thf('6', plain,
% 0.62/0.80      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.62/0.80         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      ((((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.62/0.80          != (k2_wellord1 @ sk_C @ sk_A))
% 0.62/0.80        | ~ (v1_relat_1 @ sk_C))),
% 0.62/0.80      inference('sup-', [status(thm)], ['5', '6'])).
% 0.62/0.80  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(t71_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.62/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.62/0.80  thf('9', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t97_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.62/0.80         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X41 : $i, X42 : $i]:
% 0.62/0.80         (~ (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 0.62/0.80          | ((k7_relat_1 @ X41 @ X42) = (X41))
% 0.62/0.80          | ~ (v1_relat_1 @ X41))),
% 0.62/0.80      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.62/0.80  thf('11', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.62/0.80  thf('12', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X0 @ X1)
% 0.62/0.80          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.62/0.80      inference('sup-', [status(thm)], ['8', '13'])).
% 0.62/0.80  thf(t148_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.62/0.80  thf('15', plain,
% 0.62/0.80      (![X33 : $i, X34 : $i]:
% 0.62/0.80         (((k2_relat_1 @ (k7_relat_1 @ X33 @ X34)) = (k9_relat_1 @ X33 @ X34))
% 0.62/0.80          | ~ (v1_relat_1 @ X33))),
% 0.62/0.80      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.62/0.80  thf('16', plain,
% 0.62/0.80      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 0.62/0.80          = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.62/0.80        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['14', '15'])).
% 0.62/0.80  thf('17', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t43_funct_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.62/0.80       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.80  thf('18', plain,
% 0.62/0.80      (![X43 : $i, X44 : $i]:
% 0.62/0.80         ((k5_relat_1 @ (k6_relat_1 @ X44) @ (k6_relat_1 @ X43))
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X43 @ X44)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X26 : $i, X27 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.62/0.80      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (![X43 : $i, X44 : $i]:
% 0.62/0.80         ((k5_relat_1 @ (k6_relat_1 @ X44) @ (k6_relat_1 @ X43))
% 0.62/0.80           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X43 @ X44))))),
% 0.62/0.80      inference('demod', [status(thm)], ['18', '19'])).
% 0.62/0.80  thf(t160_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ A ) =>
% 0.62/0.80       ( ![B:$i]:
% 0.62/0.80         ( ( v1_relat_1 @ B ) =>
% 0.62/0.80           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.62/0.80             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X35 : $i, X36 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X35)
% 0.62/0.80          | ((k2_relat_1 @ (k5_relat_1 @ X36 @ X35))
% 0.62/0.80              = (k9_relat_1 @ X35 @ (k2_relat_1 @ X36)))
% 0.62/0.80          | ~ (v1_relat_1 @ X36))),
% 0.62/0.80      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.62/0.80  thf('22', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k2_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.62/0.80            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.62/0.80               (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['20', '21'])).
% 0.62/0.80  thf('23', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('24', plain, (![X38 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('25', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('26', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.62/0.80           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['22', '23', '24', '25', '26'])).
% 0.62/0.80  thf('28', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.62/0.80  thf('29', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.62/0.80      inference('demod', [status(thm)], ['16', '17', '27', '28'])).
% 0.62/0.80  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.62/0.80      inference('demod', [status(thm)], ['7', '29', '30'])).
% 0.62/0.80  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
