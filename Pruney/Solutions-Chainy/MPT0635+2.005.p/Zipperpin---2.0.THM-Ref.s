%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c5Rd02tobi

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:52 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   65 (  95 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  464 ( 903 expanded)
%              Number of equality atoms :   17 (  44 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(fc2_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_funct_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( X24
       != ( k1_funct_1 @ X23 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( k1_funct_1 @ X23 @ X22 ) ) @ X23 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36','37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c5Rd02tobi
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 209 iterations in 0.106s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.37/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(fc2_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_relat_1 @ B ) & 
% 0.37/0.55         ( v1_funct_1 @ B ) ) =>
% 0.37/0.55       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 0.37/0.55         ( v1_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i]:
% 0.37/0.55         (~ (v1_funct_1 @ X18)
% 0.37/0.55          | ~ (v1_relat_1 @ X18)
% 0.37/0.55          | ~ (v1_relat_1 @ X19)
% 0.37/0.55          | ~ (v1_funct_1 @ X19)
% 0.37/0.55          | (v1_funct_1 @ (k5_relat_1 @ X18 @ X19)))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc2_funct_1])).
% 0.37/0.55  thf(dt_k5_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.37/0.55       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X12)
% 0.37/0.55          | ~ (v1_relat_1 @ X13)
% 0.37/0.55          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.37/0.55      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.55  thf(t38_funct_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.55       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.37/0.55         ( ( k1_funct_1 @ C @ A ) =
% 0.37/0.55           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.55          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.37/0.55            ( ( k1_funct_1 @ C @ A ) =
% 0.37/0.55              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(commutativity_k2_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.55  thf(t12_setfam_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X10 : $i, X11 : $i]:
% 0.37/0.55         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '7'])).
% 0.37/0.55  thf(d4_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X1)
% 0.37/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.55  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '7'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.55  thf('15', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '14'])).
% 0.37/0.55  thf(t8_funct_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.37/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.37/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.37/0.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.37/0.55          | ((X24) != (k1_funct_1 @ X23 @ X22))
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.37/0.55          | ~ (v1_funct_1 @ X23)
% 0.37/0.55          | ~ (v1_relat_1 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X23)
% 0.37/0.55          | ~ (v1_funct_1 @ X23)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X22 @ (k1_funct_1 @ X23 @ X22)) @ X23)
% 0.37/0.55          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X23)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)
% 0.37/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.37/0.55  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ sk_C)),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.37/0.55  thf(t74_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ D ) =>
% 0.37/0.55       ( ( r2_hidden @
% 0.37/0.55           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.37/0.55         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X14 @ X15)
% 0.37/0.55          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X17)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ X14 @ X16) @ 
% 0.37/0.55             (k5_relat_1 @ (k6_relat_1 @ X15) @ X17))
% 0.37/0.55          | ~ (v1_relat_1 @ X17))),
% 0.37/0.55      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ sk_C)
% 0.37/0.55          | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55             (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))
% 0.37/0.55          | ~ (r2_hidden @ sk_A @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55           (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))
% 0.37/0.55          | ~ (r2_hidden @ sk_A @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.37/0.55        (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.55         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.37/0.55          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.37/0.55          | ~ (v1_funct_1 @ X23)
% 0.37/0.55          | ~ (v1_relat_1 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.37/0.55        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.37/0.55        | ((k1_funct_1 @ sk_C @ sk_A)
% 0.37/0.55            = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (((k1_funct_1 @ sk_C @ sk_A)
% 0.37/0.55         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))
% 0.37/0.55        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.37/0.55        | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '30'])).
% 0.37/0.55  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(fc3_funct_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.37/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.37/0.55  thf('33', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C))),
% 0.37/0.55      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.37/0.55        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.37/0.55        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '34'])).
% 0.37/0.55  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('38', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.55  thf('39', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.37/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.37/0.55  thf('40', plain, ($false),
% 0.37/0.55      inference('demod', [status(thm)], ['35', '36', '37', '38', '39'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
