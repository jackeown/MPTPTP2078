%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cq7TKOPVLZ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 145 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  549 (1153 expanded)
%              Number of equality atoms :   46 ( 103 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

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

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X29 ) @ X30 )
      | ( ( k7_relat_1 @ X29 @ X30 )
        = X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_B )
    | ( ( k3_xboole_0 @ sk_C @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('38',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) @ X18 )
        = ( k7_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cq7TKOPVLZ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.84  % Solved by: fo/fo7.sh
% 0.58/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.84  % done 671 iterations in 0.383s
% 0.58/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.84  % SZS output start Refutation
% 0.58/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.58/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.84  thf(t148_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.58/0.84  thf('0', plain,
% 0.58/0.84      (![X21 : $i, X22 : $i]:
% 0.58/0.84         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.58/0.84          | ~ (v1_relat_1 @ X21))),
% 0.58/0.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.84  thf(d10_xboole_0, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.84  thf('1', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.58/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.84  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.58/0.84      inference('simplify', [status(thm)], ['1'])).
% 0.58/0.84  thf(t97_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.58/0.84         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.58/0.84  thf('3', plain,
% 0.58/0.84      (![X29 : $i, X30 : $i]:
% 0.58/0.84         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.58/0.84          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.58/0.84          | ~ (v1_relat_1 @ X29))),
% 0.58/0.84      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.58/0.84  thf('4', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.84  thf(t162_relat_1, conjecture,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) =>
% 0.58/0.84       ( ![B:$i,C:$i]:
% 0.58/0.84         ( ( r1_tarski @ B @ C ) =>
% 0.58/0.84           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.58/0.84             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.84    (~( ![A:$i]:
% 0.58/0.84        ( ( v1_relat_1 @ A ) =>
% 0.58/0.84          ( ![B:$i,C:$i]:
% 0.58/0.84            ( ( r1_tarski @ B @ C ) =>
% 0.58/0.84              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.58/0.84                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.58/0.84    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.58/0.84  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf(t71_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.58/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.84  thf('6', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('7', plain,
% 0.58/0.84      (![X29 : $i, X30 : $i]:
% 0.58/0.84         (~ (r1_tarski @ (k1_relat_1 @ X29) @ X30)
% 0.58/0.84          | ((k7_relat_1 @ X29 @ X30) = (X29))
% 0.58/0.84          | ~ (v1_relat_1 @ X29))),
% 0.58/0.84      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.58/0.84  thf('8', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.58/0.84          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.84  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.58/0.84  thf('9', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('10', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ X1)
% 0.58/0.84          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.84  thf('11', plain,
% 0.58/0.84      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.58/0.84      inference('sup-', [status(thm)], ['5', '10'])).
% 0.58/0.84  thf(t100_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i,C:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ C ) =>
% 0.58/0.84       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.58/0.84         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.58/0.84  thf('12', plain,
% 0.58/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.84         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 0.58/0.84            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 0.58/0.84          | ~ (v1_relat_1 @ X16))),
% 0.58/0.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.58/0.84  thf('13', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.58/0.84            = (k7_relat_1 @ (k6_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_C @ X0)))
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.84  thf('14', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('15', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.58/0.84           = (k7_relat_1 @ (k6_relat_1 @ sk_B) @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['13', '14'])).
% 0.58/0.84  thf(t90_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.58/0.84         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.84  thf('16', plain,
% 0.58/0.84      (![X27 : $i, X28 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k7_relat_1 @ X27 @ X28))
% 0.58/0.84            = (k3_xboole_0 @ (k1_relat_1 @ X27) @ X28))
% 0.58/0.84          | ~ (v1_relat_1 @ X27))),
% 0.58/0.84      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.58/0.84  thf('17', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 0.58/0.84            = (k3_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ 
% 0.58/0.84               (k3_xboole_0 @ sk_C @ X0)))
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['15', '16'])).
% 0.58/0.84  thf('18', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('19', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('20', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 0.58/0.84           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.58/0.84      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.58/0.84  thf('21', plain,
% 0.58/0.84      ((((k1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.58/0.84          = (k3_xboole_0 @ sk_B @ 
% 0.58/0.84             (k3_xboole_0 @ sk_C @ (k1_relat_1 @ (k6_relat_1 @ sk_B)))))
% 0.58/0.84        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['4', '20'])).
% 0.58/0.84  thf('22', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('23', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('24', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('25', plain,
% 0.58/0.84      (((sk_B) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.58/0.84      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.58/0.84  thf('26', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('27', plain,
% 0.58/0.84      (![X27 : $i, X28 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k7_relat_1 @ X27 @ X28))
% 0.58/0.84            = (k3_xboole_0 @ (k1_relat_1 @ X27) @ X28))
% 0.58/0.84          | ~ (v1_relat_1 @ X27))),
% 0.58/0.84      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.58/0.84  thf(t87_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.58/0.84  thf('28', plain,
% 0.58/0.84      (![X25 : $i, X26 : $i]:
% 0.58/0.84         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X25 @ X26)) @ X26)
% 0.58/0.84          | ~ (v1_relat_1 @ X25))),
% 0.58/0.84      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.58/0.84  thf('29', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ X1))),
% 0.58/0.84      inference('sup+', [status(thm)], ['27', '28'])).
% 0.58/0.84  thf('30', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X1)
% 0.58/0.84          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['29'])).
% 0.58/0.84  thf('31', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['26', '30'])).
% 0.58/0.84  thf('32', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.58/0.84  thf('33', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 0.58/0.84      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.84  thf('34', plain,
% 0.58/0.84      (![X0 : $i, X2 : $i]:
% 0.58/0.84         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.58/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.84  thf('35', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.58/0.84          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.84  thf('36', plain,
% 0.58/0.84      ((~ (r1_tarski @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_B)
% 0.58/0.84        | ((k3_xboole_0 @ sk_C @ sk_B)
% 0.58/0.84            = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B))))),
% 0.58/0.84      inference('sup-', [status(thm)], ['25', '35'])).
% 0.58/0.84  thf('37', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X1)),
% 0.58/0.84      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.84  thf('38', plain,
% 0.58/0.84      (((sk_B) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.58/0.84      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.58/0.84  thf('39', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.58/0.84      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.58/0.84  thf('40', plain,
% 0.58/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.84         (((k7_relat_1 @ (k7_relat_1 @ X16 @ X17) @ X18)
% 0.58/0.84            = (k7_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18)))
% 0.58/0.84          | ~ (v1_relat_1 @ X16))),
% 0.58/0.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.58/0.84  thf('41', plain,
% 0.58/0.84      (![X21 : $i, X22 : $i]:
% 0.58/0.84         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.58/0.84          | ~ (v1_relat_1 @ X21))),
% 0.58/0.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.84  thf('42', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.84            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X2)
% 0.58/0.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.84  thf(dt_k7_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.58/0.84  thf('43', plain,
% 0.58/0.84      (![X14 : $i, X15 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.58/0.84  thf('44', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X2)
% 0.58/0.84          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.84              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.58/0.84      inference('clc', [status(thm)], ['42', '43'])).
% 0.58/0.84  thf('45', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (((k2_relat_1 @ (k7_relat_1 @ X0 @ sk_B))
% 0.58/0.84            = (k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B))
% 0.58/0.84          | ~ (v1_relat_1 @ X0))),
% 0.58/0.84      inference('sup+', [status(thm)], ['39', '44'])).
% 0.58/0.84  thf('46', plain,
% 0.58/0.84      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.58/0.84         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('47', plain,
% 0.58/0.84      ((((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.58/0.84          != (k9_relat_1 @ sk_A @ sk_B))
% 0.58/0.84        | ~ (v1_relat_1 @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.84  thf('48', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('49', plain,
% 0.58/0.84      (((k2_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.58/0.84      inference('demod', [status(thm)], ['47', '48'])).
% 0.58/0.84  thf('50', plain,
% 0.58/0.84      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 0.58/0.84        | ~ (v1_relat_1 @ sk_A))),
% 0.58/0.84      inference('sup-', [status(thm)], ['0', '49'])).
% 0.58/0.84  thf('51', plain, ((v1_relat_1 @ sk_A)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('52', plain,
% 0.58/0.84      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.58/0.84      inference('demod', [status(thm)], ['50', '51'])).
% 0.58/0.84  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.58/0.84  
% 0.58/0.84  % SZS output end Refutation
% 0.58/0.84  
% 0.58/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
