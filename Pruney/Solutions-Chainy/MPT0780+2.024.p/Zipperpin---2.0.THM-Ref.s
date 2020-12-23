%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vQr35bbCeA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  72 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  410 ( 522 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X51 @ X53 ) @ X52 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X51 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X48 @ X49 ) @ X50 )
        = ( k2_wellord1 @ X48 @ ( k3_xboole_0 @ X49 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X48 @ X49 ) @ X50 )
        = ( k2_wellord1 @ X48 @ ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
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
    ! [X38: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X38 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X40 ) @ X41 )
      | ( ( k7_relat_1 @ X40 @ X41 )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

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
    ! [X34: $i,X35: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) )
        = ( k9_relat_1 @ X34 @ X35 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ ( k6_relat_1 @ X44 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ ( k6_relat_1 @ X44 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X37 @ X36 ) )
        = ( k9_relat_1 @ X36 @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X39: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X42: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vQr35bbCeA
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 13:30:30 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.32  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 90 iterations in 0.062s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t27_wellord1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.19/0.49         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.19/0.49         (((k2_wellord1 @ (k2_wellord1 @ X51 @ X53) @ X52)
% 0.19/0.49            = (k2_wellord1 @ (k2_wellord1 @ X51 @ X52) @ X53))
% 0.19/0.49          | ~ (v1_relat_1 @ X51))),
% 0.19/0.49      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.19/0.49  thf(t26_wellord1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.19/0.49         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.19/0.49         (((k2_wellord1 @ (k2_wellord1 @ X48 @ X49) @ X50)
% 0.19/0.49            = (k2_wellord1 @ X48 @ (k3_xboole_0 @ X49 @ X50)))
% 0.19/0.49          | ~ (v1_relat_1 @ X48))),
% 0.19/0.49      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.19/0.49  thf(t12_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.19/0.49         (((k2_wellord1 @ (k2_wellord1 @ X48 @ X49) @ X50)
% 0.19/0.49            = (k2_wellord1 @ X48 @ (k1_setfam_1 @ (k2_tarski @ X49 @ X50))))
% 0.19/0.49          | ~ (v1_relat_1 @ X48))),
% 0.19/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.19/0.49            = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))
% 0.19/0.49          | ~ (v1_relat_1 @ X2)
% 0.19/0.49          | ~ (v1_relat_1 @ X2))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '3'])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X2)
% 0.19/0.49          | ((k2_wellord1 @ (k2_wellord1 @ X2 @ X1) @ X0)
% 0.19/0.49              = (k2_wellord1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.49  thf(t29_wellord1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.49           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ C ) =>
% 0.19/0.49          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.19/0.49              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.49         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((((k2_wellord1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.19/0.49          != (k2_wellord1 @ sk_C @ sk_A))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t71_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.49  thf('9', plain, (![X38 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X38)) = (X38))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf(t97_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.49         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X40 : $i, X41 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k1_relat_1 @ X40) @ X41)
% 0.19/0.49          | ((k7_relat_1 @ X40 @ X41) = (X40))
% 0.19/0.49          | ~ (v1_relat_1 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(fc3_funct_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('12', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.50          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '13'])).
% 0.19/0.50  thf(t148_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X34 : $i, X35 : $i]:
% 0.19/0.50         (((k2_relat_1 @ (k7_relat_1 @ X34 @ X35)) = (k9_relat_1 @ X34 @ X35))
% 0.19/0.50          | ~ (v1_relat_1 @ X34))),
% 0.19/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((((k2_relat_1 @ (k6_relat_1 @ sk_A))
% 0.19/0.50          = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.19/0.50        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.50  thf('17', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('18', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('19', plain, (((sk_A) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.19/0.50  thf(t43_funct_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.50       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X44 : $i, X45 : $i]:
% 0.19/0.50         ((k5_relat_1 @ (k6_relat_1 @ X45) @ (k6_relat_1 @ X44))
% 0.19/0.50           = (k6_relat_1 @ (k3_xboole_0 @ X44 @ X45)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X26 : $i, X27 : $i]:
% 0.19/0.50         ((k1_setfam_1 @ (k2_tarski @ X26 @ X27)) = (k3_xboole_0 @ X26 @ X27))),
% 0.19/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X44 : $i, X45 : $i]:
% 0.19/0.50         ((k5_relat_1 @ (k6_relat_1 @ X45) @ (k6_relat_1 @ X44))
% 0.19/0.50           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X44 @ X45))))),
% 0.19/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf(t160_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( v1_relat_1 @ B ) =>
% 0.19/0.50           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.50             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X36 : $i, X37 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X36)
% 0.19/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X37 @ X36))
% 0.19/0.50              = (k9_relat_1 @ X36 @ (k2_relat_1 @ X37)))
% 0.19/0.50          | ~ (v1_relat_1 @ X37))),
% 0.19/0.50      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k2_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.19/0.50            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.19/0.50               (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.19/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('26', plain, (![X39 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.19/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.50  thf('27', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('28', plain, (![X42 : $i]: (v1_relat_1 @ (k6_relat_1 @ X42))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.19/0.50  thf('30', plain, (((sk_A) = (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['19', '29'])).
% 0.19/0.50  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['7', '30', '31'])).
% 0.19/0.50  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
