%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iet9Cb9ha3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:45 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 148 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  548 (1222 expanded)
%              Number of equality atoms :   50 ( 108 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k2_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ ( k6_relat_1 @ X35 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['7','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('23',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k2_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ X29 @ ( k10_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30','36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('44',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['23','42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['20','44'])).

thf('46',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iet9Cb9ha3
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 674 iterations in 0.344s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.62/0.80  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.62/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.62/0.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(t139_funct_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ C ) =>
% 0.62/0.80       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.62/0.80         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.62/0.80  thf('0', plain,
% 0.62/0.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.80         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.62/0.80            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.62/0.80          | ~ (v1_relat_1 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.62/0.80  thf(t175_funct_2, conjecture,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.80       ( ![B:$i,C:$i]:
% 0.62/0.80         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.62/0.80           ( ( k10_relat_1 @ A @ C ) =
% 0.62/0.80             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i]:
% 0.62/0.80        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.62/0.80          ( ![B:$i,C:$i]:
% 0.62/0.80            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.62/0.80              ( ( k10_relat_1 @ A @ C ) =
% 0.62/0.80                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.62/0.80  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(t71_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.62/0.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.62/0.80  thf('2', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t147_funct_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.62/0.80       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.62/0.80         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X28 : $i, X29 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X28 @ (k2_relat_1 @ X29))
% 0.62/0.80          | ((k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X28)) = (X28))
% 0.62/0.80          | ~ (v1_funct_1 @ X29)
% 0.62/0.80          | ~ (v1_relat_1 @ X29))),
% 0.62/0.80      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.62/0.80              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.80  thf(fc3_funct_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.62/0.80       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.62/0.80  thf('5', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('6', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.62/0.80          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.62/0.80              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.62/0.80      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.62/0.80  thf(t148_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X14 : $i, X15 : $i]:
% 0.62/0.80         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.62/0.80          | ~ (v1_relat_1 @ X14))),
% 0.62/0.80      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.62/0.80  thf(t94_relat_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ B ) =>
% 0.62/0.80       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.62/0.80  thf('9', plain,
% 0.62/0.80      (![X21 : $i, X22 : $i]:
% 0.62/0.80         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.62/0.80          | ~ (v1_relat_1 @ X22))),
% 0.62/0.80      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.62/0.80  thf(t43_funct_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.62/0.80       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X35 : $i, X36 : $i]:
% 0.62/0.80         ((k5_relat_1 @ (k6_relat_1 @ X36) @ (k6_relat_1 @ X35))
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X35 @ X36)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.62/0.80  thf('11', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('12', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('14', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('15', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.62/0.80           = (k3_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['13', '14'])).
% 0.62/0.80  thf('16', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['8', '15'])).
% 0.62/0.80  thf('17', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('18', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['16', '17'])).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X1 @ X0)
% 0.62/0.80          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.62/0.80      inference('demod', [status(thm)], ['7', '18'])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (((k3_xboole_0 @ sk_B @ 
% 0.62/0.80         (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.62/0.80         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.62/0.80      inference('sup-', [status(thm)], ['1', '19'])).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.80         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.62/0.80            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.62/0.80          | ~ (v1_relat_1 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.62/0.80  thf('22', plain,
% 0.62/0.80      (((k3_xboole_0 @ sk_B @ 
% 0.62/0.80         (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.62/0.80         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.62/0.80      inference('sup-', [status(thm)], ['1', '19'])).
% 0.62/0.80  thf('23', plain,
% 0.62/0.80      ((((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_B) @ 
% 0.62/0.80          (k10_relat_1 @ sk_A @ sk_C)) = (k10_relat_1 @ sk_A @ sk_C))
% 0.62/0.80        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['21', '22'])).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['16', '17'])).
% 0.62/0.80  thf(d10_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.80  thf('25', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.80  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.62/0.80      inference('simplify', [status(thm)], ['25'])).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X28 : $i, X29 : $i]:
% 0.62/0.80         (~ (r1_tarski @ X28 @ (k2_relat_1 @ X29))
% 0.62/0.80          | ((k9_relat_1 @ X29 @ (k10_relat_1 @ X29 @ X28)) = (X28))
% 0.62/0.80          | ~ (v1_funct_1 @ X29)
% 0.62/0.80          | ~ (v1_relat_1 @ X29))),
% 0.62/0.80      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.62/0.80  thf('28', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (~ (v1_relat_1 @ X0)
% 0.62/0.80          | ~ (v1_funct_1 @ X0)
% 0.62/0.80          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.62/0.80              = (k2_relat_1 @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.62/0.80  thf('29', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (((k3_xboole_0 @ X0 @ 
% 0.62/0.80            (k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.62/0.80            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.62/0.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['24', '28'])).
% 0.62/0.80  thf('30', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('31', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf(t169_relat_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_relat_1 @ A ) =>
% 0.62/0.80       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.62/0.80  thf('32', plain,
% 0.62/0.80      (![X18 : $i]:
% 0.62/0.80         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.62/0.80          | ~ (v1_relat_1 @ X18))),
% 0.62/0.80      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.62/0.80  thf('33', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.62/0.80            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.62/0.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.62/0.80  thf('34', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('35', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('36', plain,
% 0.62/0.80      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.62/0.80  thf('37', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.62/0.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.62/0.80  thf('38', plain, (![X24 : $i]: (v1_funct_1 @ (k6_relat_1 @ X24))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('39', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('40', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['29', '30', '36', '37', '38', '39'])).
% 0.62/0.80  thf('41', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.62/0.80           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('demod', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('42', plain,
% 0.62/0.80      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['40', '41'])).
% 0.62/0.80  thf('43', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.62/0.80      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.62/0.80  thf('44', plain,
% 0.62/0.80      (((k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.62/0.80         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.62/0.80      inference('demod', [status(thm)], ['23', '42', '43'])).
% 0.62/0.80  thf('45', plain,
% 0.62/0.80      (((k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))
% 0.62/0.80         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.62/0.80      inference('demod', [status(thm)], ['20', '44'])).
% 0.62/0.80  thf('46', plain,
% 0.62/0.80      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.62/0.80          = (k10_relat_1 @ sk_A @ sk_C))
% 0.62/0.80        | ~ (v1_relat_1 @ sk_A))),
% 0.62/0.80      inference('sup+', [status(thm)], ['0', '45'])).
% 0.62/0.80  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('48', plain,
% 0.62/0.80      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 0.62/0.80         = (k10_relat_1 @ sk_A @ sk_C))),
% 0.62/0.80      inference('demod', [status(thm)], ['46', '47'])).
% 0.62/0.80  thf('49', plain,
% 0.62/0.80      (((k10_relat_1 @ sk_A @ sk_C)
% 0.62/0.80         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('50', plain, ($false),
% 0.62/0.80      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
