%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RHFNpmekDc

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 120 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  522 (1046 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t155_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_relat_1])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RHFNpmekDc
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 228 iterations in 0.110s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(t153_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.53         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (((k9_relat_1 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.20/0.54            = (k2_xboole_0 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.20/0.54               (k9_relat_1 @ X13 @ X15)))
% 0.20/0.54          | ~ (v1_relat_1 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.20/0.54  thf(t39_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf(t44_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.20/0.54       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.20/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r1_tarski @ 
% 0.20/0.54           (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ X2))),
% 0.20/0.54      inference('sup+', [status(thm)], ['0', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (((k9_relat_1 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.20/0.54            = (k2_xboole_0 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.20/0.54               (k9_relat_1 @ X13 @ X15)))
% 0.20/0.54          | ~ (v1_relat_1 @ X13))),
% 0.20/0.54      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.20/0.54  thf(t43_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.54          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ X2)
% 0.20/0.54          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54             (k9_relat_1 @ X2 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.20/0.54          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.20/0.54          | ~ (v1_relat_1 @ X2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X2)
% 0.20/0.54          | ~ (v1_relat_1 @ X2)
% 0.20/0.54          | (r1_tarski @ 
% 0.20/0.54             (k4_xboole_0 @ 
% 0.20/0.54              (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54              (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['1', '7'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.20/0.54          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.54          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.20/0.54          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.20/0.54          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i]:
% 0.20/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (~ (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 0.20/0.54             (k4_xboole_0 @ X1 @ X0))
% 0.20/0.54          | ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.54              = (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.54           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.54  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.54         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.54          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.20/0.54          (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['26', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.20/0.54           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['16', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (v1_relat_1 @ X2)
% 0.20/0.54          | ~ (v1_relat_1 @ X2)
% 0.20/0.54          | (r1_tarski @ 
% 0.20/0.54             (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.20/0.54      inference('demod', [status(thm)], ['15', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r1_tarski @ 
% 0.20/0.54           (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.20/0.54           (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.20/0.54          | ~ (v1_relat_1 @ X2))),
% 0.20/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.54  thf(t155_relat_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ C ) =>
% 0.20/0.54       ( r1_tarski @
% 0.20/0.54         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.20/0.54         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( v1_relat_1 @ C ) =>
% 0.20/0.54          ( r1_tarski @
% 0.20/0.54            ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.20/0.54            ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t155_relat_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (~ (r1_tarski @ 
% 0.20/0.54          (k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.54           (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.20/0.54          (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i]:
% 0.20/0.54         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (~ (r1_tarski @ 
% 0.20/0.54          (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.20/0.54           (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.20/0.54          (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.54  thf('41', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '40'])).
% 0.20/0.54  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('43', plain, ($false), inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
