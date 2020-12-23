%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dLhSMbiyEW

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 121 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  548 ( 969 expanded)
%              Number of equality atoms :   31 (  70 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ ( k6_relat_1 @ X25 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X20 @ ( k10_relat_1 @ X20 @ X21 ) ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X23 @ X22 ) @ X24 )
      | ( r1_tarski @ X22 @ ( k10_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('29',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','41'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k3_xboole_0 @ X17 @ ( k10_relat_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dLhSMbiyEW
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 79 iterations in 0.054s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(t175_funct_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i,C:$i]:
% 0.21/0.51         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.51           ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.51             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51          ( ![B:$i,C:$i]:
% 0.21/0.51            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.21/0.51              ( ( k10_relat_1 @ A @ C ) =
% 0.21/0.51                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.21/0.51  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.51  thf('1', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.51  thf(t43_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.34/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.34/0.51  thf('2', plain,
% 0.34/0.51      (![X25 : $i, X26 : $i]:
% 0.34/0.51         ((k5_relat_1 @ (k6_relat_1 @ X26) @ (k6_relat_1 @ X25))
% 0.34/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X25 @ X26)))),
% 0.34/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.34/0.51  thf(t71_relat_1, axiom,
% 0.34/0.51    (![A:$i]:
% 0.34/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.34/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.34/0.51  thf('3', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.34/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.51  thf(t182_relat_1, axiom,
% 0.34/0.51    (![A:$i]:
% 0.34/0.51     ( ( v1_relat_1 @ A ) =>
% 0.34/0.51       ( ![B:$i]:
% 0.34/0.51         ( ( v1_relat_1 @ B ) =>
% 0.34/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.34/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.34/0.51  thf('4', plain,
% 0.34/0.51      (![X11 : $i, X12 : $i]:
% 0.34/0.51         (~ (v1_relat_1 @ X11)
% 0.34/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.34/0.51              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.34/0.51          | ~ (v1_relat_1 @ X12))),
% 0.34/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.34/0.51  thf('5', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.34/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.34/0.51          | ~ (v1_relat_1 @ X1)
% 0.34/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.34/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.34/0.51  thf(fc3_funct_1, axiom,
% 0.34/0.51    (![A:$i]:
% 0.34/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.34/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.34/0.51  thf('6', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('7', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.34/0.51            = (k10_relat_1 @ X1 @ X0))
% 0.34/0.51          | ~ (v1_relat_1 @ X1))),
% 0.34/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.34/0.51  thf('8', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.34/0.51            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.34/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.34/0.51      inference('sup+', [status(thm)], ['2', '7'])).
% 0.34/0.51  thf('9', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.34/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.51  thf('10', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('11', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.34/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.34/0.51  thf(t145_funct_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.34/0.51  thf('12', plain,
% 0.34/0.51      (![X20 : $i, X21 : $i]:
% 0.34/0.51         ((r1_tarski @ (k9_relat_1 @ X20 @ (k10_relat_1 @ X20 @ X21)) @ X21)
% 0.34/0.51          | ~ (v1_funct_1 @ X20)
% 0.34/0.51          | ~ (v1_relat_1 @ X20))),
% 0.34/0.51      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.34/0.51  thf('13', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((r1_tarski @ 
% 0.34/0.51           (k9_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ X1)
% 0.34/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.34/0.51          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.34/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.34/0.51  thf('14', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('15', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('16', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (r1_tarski @ 
% 0.34/0.51          (k9_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 0.34/0.51      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.34/0.51  thf('17', plain,
% 0.34/0.51      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X0)),
% 0.34/0.51      inference('sup+', [status(thm)], ['1', '16'])).
% 0.34/0.51  thf(t1_xboole_1, axiom,
% 0.34/0.51    (![A:$i,B:$i,C:$i]:
% 0.34/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.34/0.51       ( r1_tarski @ A @ C ) ))).
% 0.34/0.51  thf('18', plain,
% 0.34/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.51         (~ (r1_tarski @ X4 @ X5)
% 0.34/0.51          | ~ (r1_tarski @ X5 @ X6)
% 0.34/0.51          | (r1_tarski @ X4 @ X6))),
% 0.34/0.51      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.34/0.51  thf('19', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.34/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.34/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.34/0.51  thf('20', plain,
% 0.34/0.51      ((r1_tarski @ 
% 0.34/0.51        (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.34/0.51         (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.34/0.51        sk_B)),
% 0.34/0.51      inference('sup-', [status(thm)], ['0', '19'])).
% 0.34/0.51  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.34/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.51  thf(d10_xboole_0, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.51  thf('22', plain,
% 0.34/0.51      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.34/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.51  thf('23', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.34/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.34/0.51  thf(t163_funct_1, axiom,
% 0.34/0.51    (![A:$i,B:$i,C:$i]:
% 0.34/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.34/0.51       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.51           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.34/0.51         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.34/0.51  thf('24', plain,
% 0.34/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.51         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 0.34/0.51          | ~ (r1_tarski @ (k9_relat_1 @ X23 @ X22) @ X24)
% 0.34/0.51          | (r1_tarski @ X22 @ (k10_relat_1 @ X23 @ X24))
% 0.34/0.51          | ~ (v1_funct_1 @ X23)
% 0.34/0.51          | ~ (v1_relat_1 @ X23))),
% 0.34/0.51      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.34/0.51  thf('25', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (~ (v1_relat_1 @ X0)
% 0.34/0.51          | ~ (v1_funct_1 @ X0)
% 0.34/0.51          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.34/0.51          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.34/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.51  thf('26', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.34/0.51          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.34/0.51             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.34/0.51          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.34/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['21', '25'])).
% 0.34/0.51  thf('27', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.34/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.51  thf('28', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.34/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.34/0.51  thf('29', plain, (![X16 : $i]: (v1_funct_1 @ (k6_relat_1 @ X16))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('30', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('31', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0) @ X1)
% 0.34/0.51          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.34/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.34/0.51  thf('32', plain,
% 0.34/0.51      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.34/0.51        (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['20', '31'])).
% 0.34/0.51  thf('33', plain,
% 0.34/0.51      (![X1 : $i, X3 : $i]:
% 0.34/0.51         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.34/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.51  thf('34', plain,
% 0.34/0.51      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.34/0.51           (k10_relat_1 @ sk_A @ sk_C))
% 0.34/0.51        | ((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.34/0.51            = (k10_relat_1 @ sk_A @ sk_C)))),
% 0.34/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.51  thf('35', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.34/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.34/0.51  thf(t167_relat_1, axiom,
% 0.34/0.51    (![A:$i,B:$i]:
% 0.34/0.51     ( ( v1_relat_1 @ B ) =>
% 0.34/0.51       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.34/0.51  thf('36', plain,
% 0.34/0.51      (![X9 : $i, X10 : $i]:
% 0.34/0.51         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 0.34/0.51          | ~ (v1_relat_1 @ X9))),
% 0.34/0.51      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.34/0.51  thf('37', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.34/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.34/0.51      inference('sup+', [status(thm)], ['35', '36'])).
% 0.34/0.51  thf('38', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.34/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.34/0.51  thf('39', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.34/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.34/0.51  thf('40', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]:
% 0.34/0.51         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.34/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.34/0.51  thf('41', plain,
% 0.34/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.34/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.34/0.51  thf('42', plain,
% 0.34/0.51      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.34/0.51         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.34/0.51      inference('demod', [status(thm)], ['34', '41'])).
% 0.34/0.51  thf(t139_funct_1, axiom,
% 0.34/0.51    (![A:$i,B:$i,C:$i]:
% 0.34/0.51     ( ( v1_relat_1 @ C ) =>
% 0.34/0.51       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.34/0.51         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.34/0.51  thf('43', plain,
% 0.34/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.34/0.51         (((k10_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X19)
% 0.34/0.51            = (k3_xboole_0 @ X17 @ (k10_relat_1 @ X18 @ X19)))
% 0.34/0.51          | ~ (v1_relat_1 @ X18))),
% 0.34/0.51      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.34/0.51  thf('44', plain,
% 0.34/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.34/0.51         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('45', plain,
% 0.34/0.51      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.34/0.51          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.34/0.51        | ~ (v1_relat_1 @ sk_A))),
% 0.34/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.51  thf('46', plain, ((v1_relat_1 @ sk_A)),
% 0.34/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.51  thf('47', plain,
% 0.34/0.51      (((k10_relat_1 @ sk_A @ sk_C)
% 0.34/0.51         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.34/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.34/0.51  thf('48', plain, ($false),
% 0.34/0.51      inference('simplify_reflect-', [status(thm)], ['42', '47'])).
% 0.34/0.51  
% 0.34/0.51  % SZS output end Refutation
% 0.34/0.51  
% 0.34/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
