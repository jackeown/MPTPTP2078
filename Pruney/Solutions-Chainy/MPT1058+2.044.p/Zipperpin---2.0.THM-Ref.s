%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l13vwdWRbB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:43 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 136 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  505 (1054 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','18','19'])).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X14 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('29',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
        = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('42',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('44',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l13vwdWRbB
% 0.15/0.37  % Computer   : n024.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 18:33:51 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 91 iterations in 0.057s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.54  thf(t71_relat_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.24/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.24/0.54  thf('0', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf(d10_xboole_0, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.24/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.54  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.24/0.54  thf(t146_funct_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.24/0.54         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.24/0.54  thf('3', plain,
% 0.24/0.54      (![X27 : $i, X28 : $i]:
% 0.24/0.54         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 0.24/0.54          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X27)))
% 0.24/0.54          | ~ (v1_relat_1 @ X28))),
% 0.24/0.54      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (~ (v1_relat_1 @ X0)
% 0.24/0.54          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.24/0.54             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((r1_tarski @ X0 @ 
% 0.24/0.54           (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.24/0.54            (k9_relat_1 @ (k6_relat_1 @ X0) @ (k1_relat_1 @ (k6_relat_1 @ X0)))))
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['0', '4'])).
% 0.24/0.54  thf('6', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf('7', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.24/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.24/0.54  thf(t97_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.24/0.54         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      (![X20 : $i, X21 : $i]:
% 0.24/0.54         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.24/0.54          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 0.24/0.54          | ~ (v1_relat_1 @ X20))),
% 0.24/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['7', '10'])).
% 0.24/0.54  thf(fc3_funct_1, axiom,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.24/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.24/0.54  thf('12', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.24/0.54  thf(t148_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.24/0.54  thf('14', plain,
% 0.24/0.54      (![X12 : $i, X13 : $i]:
% 0.24/0.54         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.24/0.54          | ~ (v1_relat_1 @ X12))),
% 0.24/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.24/0.54  thf('15', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k2_relat_1 @ (k6_relat_1 @ X0))
% 0.24/0.54            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['13', '14'])).
% 0.24/0.54  thf('16', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf('17', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('18', plain,
% 0.24/0.54      (![X0 : $i]: ((X0) = (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.24/0.54  thf('19', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('20', plain,
% 0.24/0.54      (![X0 : $i]: (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.24/0.54      inference('demod', [status(thm)], ['5', '6', '18', '19'])).
% 0.24/0.54  thf('21', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf(t167_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.24/0.54  thf('22', plain,
% 0.24/0.54      (![X14 : $i, X15 : $i]:
% 0.24/0.54         ((r1_tarski @ (k10_relat_1 @ X14 @ X15) @ (k1_relat_1 @ X14))
% 0.24/0.54          | ~ (v1_relat_1 @ X14))),
% 0.24/0.54      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.24/0.54  thf('23', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.24/0.54  thf('24', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('25', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.24/0.54      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.54  thf('26', plain,
% 0.24/0.54      (![X0 : $i, X2 : $i]:
% 0.24/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.54  thf('27', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.24/0.54          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.54  thf('28', plain,
% 0.24/0.54      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['20', '27'])).
% 0.24/0.54  thf(t175_funct_2, conjecture,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.54       ( ![B:$i,C:$i]:
% 0.24/0.54         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.24/0.54           ( ( k10_relat_1 @ A @ C ) =
% 0.24/0.54             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i]:
% 0.24/0.54        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.54          ( ![B:$i,C:$i]:
% 0.24/0.54            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.24/0.54              ( ( k10_relat_1 @ A @ C ) =
% 0.24/0.54                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.24/0.54  thf('29', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('30', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.24/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.54  thf('31', plain,
% 0.24/0.54      (![X20 : $i, X21 : $i]:
% 0.24/0.54         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.24/0.54          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 0.24/0.54          | ~ (v1_relat_1 @ X20))),
% 0.24/0.54      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.24/0.54  thf('32', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.24/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.24/0.54  thf('33', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('34', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.24/0.54          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.24/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.24/0.54  thf('35', plain,
% 0.24/0.54      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 0.24/0.54         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['29', '34'])).
% 0.24/0.54  thf(t139_funct_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ C ) =>
% 0.24/0.54       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.24/0.54         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.24/0.54  thf('36', plain,
% 0.24/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.54         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 0.24/0.54            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 0.24/0.54          | ~ (v1_relat_1 @ X25))),
% 0.24/0.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.24/0.54  thf('37', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)
% 0.24/0.54            = (k3_xboole_0 @ sk_B @ 
% 0.24/0.54               (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)))
% 0.24/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.24/0.54  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (k6_relat_1 @ X22))),
% 0.24/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.24/0.54  thf('39', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)
% 0.24/0.54           = (k3_xboole_0 @ sk_B @ 
% 0.24/0.54              (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ X0)))),
% 0.24/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.24/0.54  thf('40', plain,
% 0.24/0.54      (((k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.24/0.54         (k10_relat_1 @ sk_A @ sk_C))
% 0.24/0.54         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.24/0.54      inference('sup+', [status(thm)], ['28', '39'])).
% 0.24/0.54  thf('41', plain,
% 0.24/0.54      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['20', '27'])).
% 0.24/0.54  thf('42', plain,
% 0.24/0.54      (((k10_relat_1 @ sk_A @ sk_C)
% 0.24/0.54         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.24/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.54  thf('43', plain,
% 0.24/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.54         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 0.24/0.54            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 0.24/0.54          | ~ (v1_relat_1 @ X25))),
% 0.24/0.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.24/0.54  thf('44', plain,
% 0.24/0.54      (((k10_relat_1 @ sk_A @ sk_C)
% 0.24/0.54         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('45', plain,
% 0.24/0.54      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.24/0.54          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.24/0.54        | ~ (v1_relat_1 @ sk_A))),
% 0.24/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.24/0.54  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('47', plain,
% 0.24/0.54      (((k10_relat_1 @ sk_A @ sk_C)
% 0.24/0.54         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.24/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.24/0.54  thf('48', plain, ($false),
% 0.24/0.54      inference('simplify_reflect-', [status(thm)], ['42', '47'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
