%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z9z28JYIrc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:51 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   71 (  95 expanded)
%              Number of leaves         :   24 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  439 ( 818 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X21 @ X22 ) @ ( k10_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_relat_1 @ X25 ) )
      | ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
        = ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_relat_1 @ X25 ) )
      | ( ( k9_relat_1 @ X25 @ ( k10_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['21','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z9z28JYIrc
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 384 iterations in 0.149s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(t158_funct_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.60       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.41/0.60           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.41/0.60         ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.60        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.60          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.41/0.60              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.41/0.60            ( r1_tarski @ A @ B ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.41/0.60  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t137_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.60       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.41/0.60         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.60         (((k10_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23))
% 0.41/0.60            = (k3_xboole_0 @ (k10_relat_1 @ X21 @ X22) @ 
% 0.41/0.60               (k10_relat_1 @ X21 @ X23)))
% 0.41/0.60          | ~ (v1_funct_1 @ X21)
% 0.41/0.60          | ~ (v1_relat_1 @ X21))),
% 0.41/0.60      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t28_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.41/0.60         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      ((((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.41/0.60          = (k10_relat_1 @ sk_C @ sk_A))
% 0.41/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.41/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.41/0.60  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.41/0.60         = (k10_relat_1 @ sk_C @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.41/0.60  thf('9', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(t17_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.41/0.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.41/0.60  thf(t12_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i]:
% 0.41/0.60         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.60  thf(t11_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.60         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.41/0.60      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '14'])).
% 0.41/0.60  thf(t147_funct_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.60       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.41/0.60         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X24 @ (k2_relat_1 @ X25))
% 0.41/0.60          | ((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24)) = (X24))
% 0.41/0.60          | ~ (v1_funct_1 @ X25)
% 0.41/0.60          | ~ (v1_relat_1 @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ sk_C)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60          | ((k9_relat_1 @ sk_C @ 
% 0.41/0.60              (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))
% 0.41/0.60              = (k3_xboole_0 @ sk_A @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ X0)))
% 0.41/0.60           = (k3_xboole_0 @ sk_A @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.41/0.60         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.41/0.60      inference('sup+', [status(thm)], ['8', '20'])).
% 0.41/0.60  thf('22', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X24 @ (k2_relat_1 @ X25))
% 0.41/0.60          | ((k9_relat_1 @ X25 @ (k10_relat_1 @ X25 @ X24)) = (X24))
% 0.41/0.60          | ~ (v1_funct_1 @ X25)
% 0.41/0.60          | ~ (v1_relat_1 @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.60        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.60  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.41/0.60  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['21', '27'])).
% 0.41/0.60  thf(t100_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X6 @ X7)
% 0.41/0.60           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X6 : $i, X7 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X6 @ X7)
% 0.41/0.60           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.60  thf(l32_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X3 : $i, X5 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.41/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.60  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['36', '39'])).
% 0.41/0.60  thf('41', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['30', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X3 : $i, X4 : $i]:
% 0.41/0.60         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.60  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.44/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
