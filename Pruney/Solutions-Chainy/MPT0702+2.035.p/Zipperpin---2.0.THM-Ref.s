%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cAYYFSdGUv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:47 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 167 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  481 (1837 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( r1_tarski @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( r1_tarski @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X17 ) ) @ X17 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( r1_tarski @ X14 @ ( k10_relat_1 @ X15 @ ( k9_relat_1 @ X15 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k6_subset_1 @ X12 @ X13 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X11 @ X12 ) @ ( k10_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k10_relat_1 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X11 @ X12 ) @ ( k10_relat_1 @ X11 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('32',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('35',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cAYYFSdGUv
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:52:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 76 iterations in 0.052s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.34/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(t157_funct_1, conjecture,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.52       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.34/0.52           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.34/0.52         ( r1_tarski @ A @ B ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.52          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.34/0.52              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.34/0.52            ( r1_tarski @ A @ B ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.34/0.52  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t152_funct_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.52       ( ( v2_funct_1 @ B ) =>
% 0.34/0.52         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (~ (v2_funct_1 @ X16)
% 0.34/0.52          | (r1_tarski @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X17)) @ X17)
% 0.34/0.52          | ~ (v1_funct_1 @ X16)
% 0.34/0.52          | ~ (v1_relat_1 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(l32_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X3 : $i, X5 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.34/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.34/0.52         = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (~ (v2_funct_1 @ X16)
% 0.34/0.52          | (r1_tarski @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X17)) @ X17)
% 0.34/0.52          | ~ (v1_funct_1 @ X16)
% 0.34/0.52          | ~ (v1_relat_1 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.34/0.52  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t146_funct_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.34/0.52         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X14 : $i, X15 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.34/0.52          | (r1_tarski @ X14 @ (k10_relat_1 @ X15 @ (k9_relat_1 @ X15 @ X14)))
% 0.34/0.52          | ~ (v1_relat_1 @ X15))),
% 0.34/0.52      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.52        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.52  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.34/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i]:
% 0.34/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.34/0.52        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.52        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '12'])).
% 0.34/0.52  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('16', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.34/0.52  thf(t138_funct_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.52       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.34/0.52         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.52         (((k10_relat_1 @ X11 @ (k6_subset_1 @ X12 @ X13))
% 0.34/0.52            = (k6_subset_1 @ (k10_relat_1 @ X11 @ X12) @ 
% 0.34/0.52               (k10_relat_1 @ X11 @ X13)))
% 0.34/0.52          | ~ (v1_funct_1 @ X11)
% 0.34/0.52          | ~ (v1_relat_1 @ X11))),
% 0.34/0.52      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.34/0.52  thf(redefinition_k6_subset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.52         (((k10_relat_1 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.34/0.52            = (k4_xboole_0 @ (k10_relat_1 @ X11 @ X12) @ 
% 0.34/0.52               (k10_relat_1 @ X11 @ X13)))
% 0.34/0.52          | ~ (v1_funct_1 @ X11)
% 0.34/0.52          | ~ (v1_relat_1 @ X11))),
% 0.34/0.52      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (((k10_relat_1 @ sk_C @ 
% 0.34/0.52            (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0))
% 0.34/0.52            = (k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ X0)))
% 0.34/0.52          | ~ (v1_relat_1 @ sk_C)
% 0.34/0.52          | ~ (v1_funct_1 @ sk_C))),
% 0.34/0.52      inference('sup+', [status(thm)], ['17', '21'])).
% 0.34/0.52  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((k10_relat_1 @ sk_C @ (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0))
% 0.34/0.52           = (k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ X0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (((k10_relat_1 @ sk_C @ k1_xboole_0)
% 0.34/0.52         = (k4_xboole_0 @ sk_A @ 
% 0.34/0.52            (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['4', '25'])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.34/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X3 : $i, X5 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.34/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.52  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((k10_relat_1 @ sk_C @ (k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0))
% 0.34/0.52           = (k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ X0)))),
% 0.34/0.52      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (((k10_relat_1 @ sk_C @ k1_xboole_0)
% 0.34/0.52         = (k4_xboole_0 @ sk_A @ 
% 0.34/0.52            (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.34/0.52  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('35', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.52      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      (((k1_xboole_0)
% 0.34/0.52         = (k4_xboole_0 @ sk_A @ 
% 0.34/0.52            (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['26', '35'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (![X3 : $i, X4 : $i]:
% 0.34/0.52         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.34/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.52        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.34/0.52  thf(t1_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.34/0.52       ( r1_tarski @ A @ C ) ))).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X6 @ X7)
% 0.34/0.52          | ~ (r1_tarski @ X7 @ X8)
% 0.34/0.52          | (r1_tarski @ X6 @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         ((r1_tarski @ sk_A @ X0)
% 0.34/0.52          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.34/0.52               X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.34/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.34/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.34/0.52        | (r1_tarski @ sk_A @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '41'])).
% 0.34/0.52  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.34/0.52      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.34/0.52  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
