%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kt6Tv7Lh2F

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:51 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 168 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  463 (1475 expanded)
%              Number of equality atoms :   38 (  87 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k6_subset_1 @ X19 @ X20 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
        = ( k6_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) ) )
      = ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('29',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) )
    = ( k6_subset_1 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('31',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k6_subset_1 @ X19 @ X20 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
        = ( k6_subset_1 @ k1_xboole_0 @ ( k10_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','38','39','40'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('44',plain,
    ( ( k9_relat_1 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','42','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kt6Tv7Lh2F
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:06:07 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 215 iterations in 0.094s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(t158_funct_1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.37/0.56           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.37/0.56         ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.37/0.56              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.37/0.56            ( r1_tarski @ A @ B ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.37/0.56  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(l32_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i]:
% 0.37/0.56         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.37/0.56         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.56  thf(t138_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.56       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.37/0.56         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.56         (((k10_relat_1 @ X18 @ (k6_subset_1 @ X19 @ X20))
% 0.37/0.56            = (k6_subset_1 @ (k10_relat_1 @ X18 @ X19) @ 
% 0.37/0.56               (k10_relat_1 @ X18 @ X20)))
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.37/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56        | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.37/0.56  thf('11', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t36_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.37/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf(t1_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.56       ( r1_tarski @ A @ C ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X6 @ X7)
% 0.37/0.56          | ~ (r1_tarski @ X7 @ X8)
% 0.37/0.56          | (r1_tarski @ X6 @ X8))),
% 0.37/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['11', '16'])).
% 0.37/0.56  thf(t147_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.37/0.56         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X21 @ (k2_relat_1 @ X22))
% 0.37/0.56          | ((k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X21)) = (X21))
% 0.37/0.56          | ~ (v1_funct_1 @ X22)
% 0.37/0.56          | ~ (v1_relat_1 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ sk_C)
% 0.37/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.56          | ((k9_relat_1 @ sk_C @ 
% 0.37/0.56              (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.37/0.56              = (k6_subset_1 @ sk_A @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.37/0.56           = (k6_subset_1 @ sk_A @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['10', '22'])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i]:
% 0.37/0.56         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('27', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)))
% 0.37/0.56           = (k6_subset_1 @ sk_A @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ k1_xboole_0))
% 0.37/0.56         = (k6_subset_1 @ sk_A @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.56  thf('30', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.56         (((k10_relat_1 @ X18 @ (k6_subset_1 @ X19 @ X20))
% 0.37/0.56            = (k6_subset_1 @ (k10_relat_1 @ X18 @ X19) @ 
% 0.37/0.56               (k10_relat_1 @ X18 @ X20)))
% 0.37/0.56          | ~ (v1_funct_1 @ X18)
% 0.37/0.56          | ~ (v1_relat_1 @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k10_relat_1 @ sk_C @ 
% 0.37/0.56            (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0))
% 0.37/0.56            = (k6_subset_1 @ k1_xboole_0 @ (k10_relat_1 @ sk_C @ X0)))
% 0.37/0.56          | ~ (v1_relat_1 @ sk_C)
% 0.37/0.56          | ~ (v1_funct_1 @ sk_C))),
% 0.37/0.56      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.56      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X3 : $i, X5 : $i]:
% 0.37/0.56         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k10_relat_1 @ sk_C @ 
% 0.37/0.56           (k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ X0)) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '38', '39', '40'])).
% 0.37/0.56  thf('42', plain, (((k10_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '41'])).
% 0.37/0.56  thf('43', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('44', plain, (((k9_relat_1 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['29', '42', '43'])).
% 0.37/0.56  thf('45', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['23', '44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i]:
% 0.37/0.56         ((k6_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '48'])).
% 0.37/0.56  thf('50', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.37/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
