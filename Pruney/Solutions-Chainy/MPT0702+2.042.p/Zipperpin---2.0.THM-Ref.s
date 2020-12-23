%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NtjrEJeY0k

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 121 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   19
%              Number of atoms          :  587 (1390 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k10_relat_1 @ X8 @ X6 ) @ ( k10_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X3 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['15','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['12','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NtjrEJeY0k
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 86 iterations in 0.098s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(t157_funct_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.56           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.56         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.56              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.56            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.21/0.56  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t152_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( v2_funct_1 @ B ) =>
% 0.21/0.56         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X12)
% 0.21/0.56          | (r1_tarski @ (k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X13)) @ X13)
% 0.21/0.56          | ~ (v1_funct_1 @ X12)
% 0.21/0.56          | ~ (v1_relat_1 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t178_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ C ) =>
% 0.21/0.56       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.56         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.56          | ~ (v1_relat_1 @ X8)
% 0.21/0.56          | (r1_tarski @ (k10_relat_1 @ X8 @ X6) @ (k10_relat_1 @ X8 @ X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.56           (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf(t1_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.56       ( r1_tarski @ A @ C ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.56          | (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ X1)
% 0.21/0.56          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.56  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.21/0.56  thf(t154_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( v2_funct_1 @ B ) =>
% 0.21/0.56         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X14)
% 0.21/0.56          | ((k9_relat_1 @ X14 @ X15)
% 0.21/0.56              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 0.21/0.56          | ~ (v1_funct_1 @ X14)
% 0.21/0.56          | ~ (v1_relat_1 @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.56  thf(t155_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( v2_funct_1 @ B ) =>
% 0.21/0.56         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X16)
% 0.21/0.56          | ((k10_relat_1 @ X16 @ X17)
% 0.21/0.56              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_relat_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.56  thf(dt_k2_funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X9 : $i]:
% 0.21/0.56         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (v1_funct_1 @ X9)
% 0.21/0.56          | ~ (v1_relat_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X9 : $i]:
% 0.21/0.56         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (v1_funct_1 @ X9)
% 0.21/0.56          | ~ (v1_relat_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.56  thf(t169_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X5 : $i]:
% 0.21/0.56         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 0.21/0.56          | ~ (v1_relat_1 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X9 : $i]:
% 0.21/0.56         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.21/0.56          | ~ (v1_funct_1 @ X9)
% 0.21/0.56          | ~ (v1_relat_1 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X16)
% 0.21/0.56          | ((k10_relat_1 @ X16 @ X17)
% 0.21/0.56              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 0.21/0.56          | ~ (v1_funct_1 @ X16)
% 0.21/0.56          | ~ (v1_relat_1 @ X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.56  thf(t144_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i]:
% 0.21/0.56         ((r1_tarski @ (k9_relat_1 @ X3 @ X4) @ (k2_relat_1 @ X3))
% 0.21/0.56          | ~ (v1_relat_1 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 0.21/0.56           (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.21/0.56          | ~ (v1_relat_1 @ X1)
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ~ (v2_funct_1 @ X1)
% 0.21/0.56          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.21/0.56             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.21/0.56           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.56          | ~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0))),
% 0.21/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v2_funct_1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['17', '23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (v2_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_funct_1 @ X0)
% 0.21/0.56          | ~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.56  thf('26', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.56          | (r1_tarski @ X0 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.56        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.56  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('33', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.21/0.56  thf(t147_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.56         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 0.21/0.56          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 0.21/0.56          | ~ (v1_funct_1 @ X11)
% 0.21/0.56          | ~ (v1_relat_1 @ X11))),
% 0.21/0.56      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.56        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))
% 0.21/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '35'])).
% 0.21/0.56  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56          (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))
% 0.21/0.56        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '39'])).
% 0.21/0.56  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.56         (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      ((((k10_relat_1 @ sk_C @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.21/0.56          = (sk_A))
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup+', [status(thm)], ['14', '43'])).
% 0.21/0.56  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (((k10_relat_1 @ sk_C @ (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 0.21/0.56         = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))
% 0.21/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.56      inference('sup+', [status(thm)], ['13', '48'])).
% 0.21/0.56  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('52', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 0.21/0.56  thf('54', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '53'])).
% 0.21/0.56  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
