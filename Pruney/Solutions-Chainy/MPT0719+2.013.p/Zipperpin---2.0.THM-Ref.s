%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xblLhoh8O

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:27 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   64 (  77 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  364 ( 431 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ( v5_funct_1 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v5_funct_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('30',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xblLhoh8O
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 589 iterations in 0.293s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.55/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.78  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.55/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.55/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.55/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.55/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.78  thf(cc1_relat_1, axiom,
% 0.55/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.55/0.78  thf('0', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.55/0.78  thf(cc1_funct_1, axiom,
% 0.55/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.55/0.78  thf('1', plain, (![X9 : $i]: ((v1_funct_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.55/0.78      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.55/0.78  thf(d20_funct_1, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( ![B:$i]:
% 0.55/0.78         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.78           ( ( v5_funct_1 @ B @ A ) <=>
% 0.55/0.78             ( ![C:$i]:
% 0.55/0.78               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.78                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (![X10 : $i, X11 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X10)
% 0.55/0.78          | ~ (v1_funct_1 @ X10)
% 0.55/0.78          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ (k1_relat_1 @ X10))
% 0.55/0.78          | (v5_funct_1 @ X10 @ X11)
% 0.55/0.78          | ~ (v1_funct_1 @ X11)
% 0.55/0.78          | ~ (v1_relat_1 @ X11))),
% 0.55/0.78      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.55/0.78  thf(t12_funct_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.55/0.78       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.55/0.78         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.55/0.78  thf('3', plain,
% 0.55/0.78      (![X13 : $i, X14 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.55/0.78          | (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ (k2_relat_1 @ X14))
% 0.55/0.78          | ~ (v1_funct_1 @ X14)
% 0.55/0.78          | ~ (v1_relat_1 @ X14))),
% 0.55/0.78      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X1)
% 0.55/0.78          | (v5_funct_1 @ X0 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ X1)) @ 
% 0.55/0.78             (k2_relat_1 @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_C_1 @ X0 @ X1)) @ 
% 0.55/0.78           (k2_relat_1 @ X0))
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | (v5_funct_1 @ X0 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X1)
% 0.55/0.78          | ~ (v1_relat_1 @ X1))),
% 0.55/0.78      inference('simplify', [status(thm)], ['4'])).
% 0.55/0.78  thf(l13_xboole_0, axiom,
% 0.55/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.55/0.78  thf('6', plain,
% 0.55/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.55/0.78  thf(t2_boole, axiom,
% 0.55/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.78  thf('7', plain,
% 0.55/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.78  thf('8', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['6', '7'])).
% 0.55/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.55/0.78  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.78  thf(fc11_relat_1, axiom,
% 0.55/0.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      (![X8 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.55/0.78  thf('12', plain,
% 0.55/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.55/0.78  thf('14', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.78  thf('15', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ~ (v1_xboole_0 @ X1)
% 0.55/0.78          | ((X1) = (k2_relat_1 @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['11', '14'])).
% 0.55/0.78  thf('16', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ((k3_xboole_0 @ X1 @ X0) = (k2_relat_1 @ X2))
% 0.55/0.78          | ~ (v1_xboole_0 @ X2))),
% 0.55/0.78      inference('sup-', [status(thm)], ['10', '15'])).
% 0.55/0.78  thf('17', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['6', '7'])).
% 0.55/0.78  thf('18', plain,
% 0.55/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.78  thf(t4_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.78            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.78  thf('19', plain,
% 0.55/0.78      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.55/0.78          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.55/0.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.78  thf('20', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.78  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.55/0.78  thf('21', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.55/0.78      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.55/0.78  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.55/0.78      inference('demod', [status(thm)], ['20', '21'])).
% 0.55/0.78  thf('23', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['17', '22'])).
% 0.55/0.78  thf('24', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X3 @ (k2_relat_1 @ X0))
% 0.55/0.78          | ~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ~ (v1_xboole_0 @ X1)
% 0.55/0.78          | ~ (v1_xboole_0 @ X1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['16', '23'])).
% 0.55/0.78  thf('25', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ X1)
% 0.55/0.78          | ~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ~ (r2_hidden @ X3 @ (k2_relat_1 @ X0)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['24'])).
% 0.55/0.78  thf('26', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('condensation', [status(thm)], ['25'])).
% 0.55/0.78  thf('27', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X1)
% 0.55/0.78          | (v5_funct_1 @ X0 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['5', '26'])).
% 0.55/0.78  thf('28', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ~ (v1_xboole_0 @ X0)
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | (v5_funct_1 @ X0 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X1)
% 0.55/0.78          | ~ (v1_relat_1 @ X1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['1', '27'])).
% 0.55/0.78  thf('29', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]:
% 0.55/0.78         (~ (v1_relat_1 @ X1)
% 0.55/0.78          | ~ (v1_funct_1 @ X1)
% 0.55/0.78          | (v5_funct_1 @ X0 @ X1)
% 0.55/0.78          | ~ (v1_relat_1 @ X0)
% 0.55/0.78          | ~ (v1_xboole_0 @ X0))),
% 0.55/0.78      inference('simplify', [status(thm)], ['28'])).
% 0.55/0.78  thf(t174_funct_1, conjecture,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i]:
% 0.55/0.78        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.78          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.55/0.78  thf('30', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('31', plain,
% 0.55/0.78      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.55/0.78        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.55/0.78        | ~ (v1_funct_1 @ sk_A)
% 0.55/0.78        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.78  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.78  thf('33', plain, ((v1_funct_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('35', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.55/0.78      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.55/0.78  thf('36', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '35'])).
% 0.55/0.78  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.78  thf('38', plain, ($false), inference('demod', [status(thm)], ['36', '37'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
