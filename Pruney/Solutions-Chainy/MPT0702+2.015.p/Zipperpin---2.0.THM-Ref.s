%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kbq6wuuEAO

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:44 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 128 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  477 (1033 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X21 @ ( k6_subset_1 @ X22 @ X23 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X21 @ X22 ) @ ( k10_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('18',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k9_relat_1 @ X18 @ ( k6_subset_1 @ X19 @ X20 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X18 @ X19 ) @ ( k9_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( r1_tarski @ X24 @ ( k10_relat_1 @ X25 @ ( k9_relat_1 @ X25 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('42',plain,
    ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('44',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k6_subset_1 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kbq6wuuEAO
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.74  % Solved by: fo/fo7.sh
% 0.49/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.74  % done 753 iterations in 0.284s
% 0.49/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.74  % SZS output start Refutation
% 0.49/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.74  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.74  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.49/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.74  thf(t157_funct_1, conjecture,
% 0.49/0.74    (![A:$i,B:$i,C:$i]:
% 0.49/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.74       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.49/0.74           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.49/0.74         ( r1_tarski @ A @ B ) ) ))).
% 0.49/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.74        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.74          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.49/0.74              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.49/0.74            ( r1_tarski @ A @ B ) ) ) )),
% 0.49/0.74    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.49/0.74  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf(t3_boole, axiom,
% 0.49/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.74  thf('1', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.49/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.74  thf(redefinition_k6_subset_1, axiom,
% 0.49/0.74    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.49/0.74  thf('2', plain,
% 0.49/0.74      (![X16 : $i, X17 : $i]:
% 0.49/0.74         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.49/0.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.74  thf('3', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 0.49/0.74      inference('demod', [status(thm)], ['1', '2'])).
% 0.49/0.74  thf(t36_xboole_1, axiom,
% 0.49/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.74  thf('4', plain,
% 0.49/0.74      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.49/0.74      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.74  thf('5', plain,
% 0.49/0.74      (![X16 : $i, X17 : $i]:
% 0.49/0.74         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.49/0.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.74  thf('6', plain,
% 0.49/0.74      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.49/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.74  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.74      inference('sup+', [status(thm)], ['3', '6'])).
% 0.49/0.74  thf(l32_xboole_1, axiom,
% 0.49/0.74    (![A:$i,B:$i]:
% 0.49/0.74     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.74  thf('8', plain,
% 0.49/0.74      (![X2 : $i, X4 : $i]:
% 0.49/0.74         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.49/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.74  thf('9', plain,
% 0.49/0.74      (![X16 : $i, X17 : $i]:
% 0.49/0.74         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.49/0.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.74  thf('10', plain,
% 0.49/0.74      (![X2 : $i, X4 : $i]:
% 0.49/0.74         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.49/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.49/0.74  thf('11', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['7', '10'])).
% 0.49/0.74  thf(t138_funct_1, axiom,
% 0.49/0.74    (![A:$i,B:$i,C:$i]:
% 0.49/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.74       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.49/0.74         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.49/0.74  thf('12', plain,
% 0.49/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.74         (((k10_relat_1 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 0.49/0.74            = (k6_subset_1 @ (k10_relat_1 @ X21 @ X22) @ 
% 0.49/0.74               (k10_relat_1 @ X21 @ X23)))
% 0.49/0.74          | ~ (v1_funct_1 @ X21)
% 0.49/0.74          | ~ (v1_relat_1 @ X21))),
% 0.49/0.74      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.49/0.74  thf('13', plain,
% 0.49/0.74      (![X0 : $i, X1 : $i]:
% 0.49/0.74         (((k10_relat_1 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))
% 0.49/0.74          | ~ (v1_relat_1 @ X1)
% 0.49/0.74          | ~ (v1_funct_1 @ X1))),
% 0.49/0.74      inference('sup+', [status(thm)], ['11', '12'])).
% 0.49/0.74  thf('14', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['7', '10'])).
% 0.49/0.74  thf('15', plain,
% 0.49/0.74      (![X1 : $i]:
% 0.49/0.74         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.49/0.74          | ~ (v1_relat_1 @ X1)
% 0.49/0.74          | ~ (v1_funct_1 @ X1))),
% 0.49/0.74      inference('demod', [status(thm)], ['13', '14'])).
% 0.49/0.74  thf('16', plain,
% 0.49/0.74      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('17', plain,
% 0.49/0.74      (![X2 : $i, X4 : $i]:
% 0.49/0.74         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.49/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.49/0.74  thf('18', plain,
% 0.49/0.74      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.49/0.74         = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.74  thf(t123_funct_1, axiom,
% 0.49/0.74    (![A:$i,B:$i,C:$i]:
% 0.49/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.74       ( ( v2_funct_1 @ C ) =>
% 0.49/0.74         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.49/0.74           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.49/0.74  thf('19', plain,
% 0.49/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.74         (~ (v2_funct_1 @ X18)
% 0.49/0.74          | ((k9_relat_1 @ X18 @ (k6_subset_1 @ X19 @ X20))
% 0.49/0.74              = (k6_subset_1 @ (k9_relat_1 @ X18 @ X19) @ 
% 0.49/0.74                 (k9_relat_1 @ X18 @ X20)))
% 0.49/0.74          | ~ (v1_funct_1 @ X18)
% 0.49/0.74          | ~ (v1_relat_1 @ X18))),
% 0.49/0.74      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.49/0.74  thf('20', plain,
% 0.49/0.74      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.49/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.74        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.74      inference('sup+', [status(thm)], ['18', '19'])).
% 0.49/0.74  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('23', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('24', plain,
% 0.49/0.74      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.49/0.74      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.49/0.74  thf('25', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('26', plain,
% 0.49/0.74      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 0.49/0.74      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.74  thf(t12_xboole_1, axiom,
% 0.49/0.74    (![A:$i,B:$i]:
% 0.49/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.49/0.74  thf('27', plain,
% 0.49/0.74      (![X8 : $i, X9 : $i]:
% 0.49/0.74         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.49/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.49/0.74  thf('28', plain,
% 0.49/0.74      (![X0 : $i, X1 : $i]:
% 0.49/0.74         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.74  thf(t11_xboole_1, axiom,
% 0.49/0.74    (![A:$i,B:$i,C:$i]:
% 0.49/0.74     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.49/0.74  thf('29', plain,
% 0.49/0.74      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.74         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.49/0.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.49/0.74  thf('30', plain,
% 0.49/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.74         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 0.49/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.74  thf('31', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.49/0.74      inference('sup-', [status(thm)], ['25', '30'])).
% 0.49/0.74  thf(t146_funct_1, axiom,
% 0.49/0.74    (![A:$i,B:$i]:
% 0.49/0.74     ( ( v1_relat_1 @ B ) =>
% 0.49/0.74       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.74         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.49/0.74  thf('32', plain,
% 0.49/0.74      (![X24 : $i, X25 : $i]:
% 0.49/0.74         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 0.49/0.74          | (r1_tarski @ X24 @ (k10_relat_1 @ X25 @ (k9_relat_1 @ X25 @ X24)))
% 0.49/0.74          | ~ (v1_relat_1 @ X25))),
% 0.49/0.74      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.49/0.74  thf('33', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (~ (v1_relat_1 @ sk_C)
% 0.49/0.74          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.49/0.74             (k10_relat_1 @ sk_C @ 
% 0.49/0.74              (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))))),
% 0.49/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.49/0.74  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('35', plain,
% 0.49/0.74      (![X0 : $i]:
% 0.49/0.74         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ 
% 0.49/0.74          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0))))),
% 0.49/0.74      inference('demod', [status(thm)], ['33', '34'])).
% 0.49/0.74  thf('36', plain,
% 0.49/0.74      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.49/0.74        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.49/0.74      inference('sup+', [status(thm)], ['24', '35'])).
% 0.49/0.74  thf('37', plain,
% 0.49/0.74      (((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.49/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.74        | ~ (v1_relat_1 @ sk_C))),
% 0.49/0.74      inference('sup+', [status(thm)], ['15', '36'])).
% 0.49/0.74  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.74  thf('40', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.49/0.74      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.49/0.74  thf('41', plain,
% 0.49/0.74      (![X2 : $i, X4 : $i]:
% 0.49/0.74         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.49/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.49/0.74  thf('42', plain,
% 0.49/0.74      (((k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.49/0.74         = (k1_xboole_0))),
% 0.49/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.74  thf('43', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 0.49/0.74      inference('demod', [status(thm)], ['1', '2'])).
% 0.49/0.74  thf('44', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.49/0.74      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.74  thf('45', plain,
% 0.49/0.74      (![X2 : $i, X3 : $i]:
% 0.49/0.74         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.49/0.74      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.74  thf('46', plain,
% 0.49/0.74      (![X16 : $i, X17 : $i]:
% 0.49/0.74         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.49/0.74      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.49/0.74  thf('47', plain,
% 0.49/0.74      (![X2 : $i, X3 : $i]:
% 0.49/0.74         ((r1_tarski @ X2 @ X3) | ((k6_subset_1 @ X2 @ X3) != (k1_xboole_0)))),
% 0.49/0.74      inference('demod', [status(thm)], ['45', '46'])).
% 0.49/0.74  thf('48', plain,
% 0.49/0.74      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.74      inference('sup-', [status(thm)], ['44', '47'])).
% 0.49/0.74  thf('49', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.49/0.74      inference('simplify', [status(thm)], ['48'])).
% 0.49/0.74  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.49/0.74  
% 0.49/0.74  % SZS output end Refutation
% 0.49/0.74  
% 0.61/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
