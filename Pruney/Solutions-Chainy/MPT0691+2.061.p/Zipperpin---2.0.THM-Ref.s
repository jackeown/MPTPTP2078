%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.plp87RUpSV

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 (  91 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  456 ( 714 expanded)
%              Number of equality atoms :   39 (  46 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( k1_relat_1 @ X46 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X46 @ X45 ) )
        = X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X40: $i] :
      ( ( ( k9_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('8',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X41 @ X42 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X43 @ X42 ) @ X41 )
        = ( k9_relat_1 @ X43 @ X41 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) @ X49 )
        = ( k3_xboole_0 @ X47 @ ( k10_relat_1 @ X48 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X44: $i] :
      ( ( ( k10_relat_1 @ X44 @ ( k2_relat_1 @ X44 ) )
        = ( k1_relat_1 @ X44 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( ( k4_xboole_0 @ X4 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.plp87RUpSV
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:00:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 100 iterations in 0.084s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(t146_funct_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ B ) =>
% 0.21/0.53          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_k7_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k7_relat_1 @ X38 @ X39)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t91_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.53         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X45 : $i, X46 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X45 @ (k1_relat_1 @ X46))
% 0.21/0.53          | ((k1_relat_1 @ (k7_relat_1 @ X46 @ X45)) = (X45))
% 0.21/0.53          | ~ (v1_relat_1 @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('6', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf(t146_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X40 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (k2_relat_1 @ X40))
% 0.21/0.53          | ~ (v1_relat_1 @ X40))),
% 0.21/0.53      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '8'])).
% 0.21/0.53  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.53         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('13', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.53  thf(t162_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i,C:$i]:
% 0.21/0.53         ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.21/0.53             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X41 @ X42)
% 0.21/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X43 @ X42) @ X41)
% 0.21/0.53              = (k9_relat_1 @ X43 @ X41))
% 0.21/0.53          | ~ (v1_relat_1 @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1)
% 0.21/0.53          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.53              = (k9_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['11', '15'])).
% 0.21/0.53  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf(t139_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.21/0.53         (((k10_relat_1 @ (k7_relat_1 @ X48 @ X47) @ X49)
% 0.21/0.53            = (k3_xboole_0 @ X47 @ (k10_relat_1 @ X48 @ X49)))
% 0.21/0.53          | ~ (v1_relat_1 @ X48))),
% 0.21/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.21/0.53  thf(t169_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X44 : $i]:
% 0.21/0.53         (((k10_relat_1 @ X44 @ (k2_relat_1 @ X44)) = (k1_relat_1 @ X44))
% 0.21/0.53          | ~ (v1_relat_1 @ X44))),
% 0.21/0.53      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X0 @ 
% 0.21/0.53            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.21/0.53            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X38 : $i, X39 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k7_relat_1 @ X38 @ X39)))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X1)
% 0.21/0.53          | ((k3_xboole_0 @ X0 @ 
% 0.21/0.53              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.21/0.53              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.21/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k3_xboole_0 @ sk_A @ 
% 0.21/0.53          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['18', '23'])).
% 0.21/0.53  thf('25', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.53  thf(l32_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.53  thf('33', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['32', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.21/0.53         = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((r1_tarski @ X4 @ X5) | ((k4_xboole_0 @ X4 @ X5) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.53  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
