%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bf5yqBEdDL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:04 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  583 (1025 expanded)
%              Number of equality atoms :   30 (  62 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t163_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t163_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k2_relat_1 @ X15 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X16 @ X17 ) @ ( k10_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
        = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','21'])).

thf('23',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['22','25'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k10_relat_1 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X16 @ X17 ) @ ( k10_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r1_tarski @ X23 @ ( k10_relat_1 @ X24 @ ( k9_relat_1 @ X24 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) @ X1 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) @ X1 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','51'])).

thf('53',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['32','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bf5yqBEdDL
% 0.15/0.35  % Computer   : n001.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:30:00 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 342 iterations in 0.146s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(t163_funct_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.61       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.61           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.38/0.61         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.61          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.61              ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.38/0.61            ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t163_funct_1])).
% 0.38/0.61  thf('0', plain, (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t71_relat_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.61  thf('1', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.61  thf(t169_relat_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ A ) =>
% 0.38/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X15 : $i]:
% 0.38/0.61         (((k10_relat_1 @ X15 @ (k2_relat_1 @ X15)) = (k1_relat_1 @ X15))
% 0.38/0.61          | ~ (v1_relat_1 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.38/0.61            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.38/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.61  thf('4', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.61  thf(fc3_funct_1, axiom,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.61  thf('5', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.61  thf(t175_relat_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ C ) =>
% 0.38/0.61       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.38/0.61         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (((k10_relat_1 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.38/0.61            = (k2_xboole_0 @ (k10_relat_1 @ X16 @ X17) @ 
% 0.38/0.61               (k10_relat_1 @ X16 @ X18)))
% 0.38/0.61          | ~ (v1_relat_1 @ X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.61            = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.38/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf('10', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.61           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.38/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf(t167_relat_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ B ) =>
% 0.38/0.61       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X13 : $i, X14 : $i]:
% 0.38/0.61         ((r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k1_relat_1 @ X13))
% 0.38/0.61          | ~ (v1_relat_1 @ X13))),
% 0.38/0.61      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.38/0.61  thf(d10_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X2 : $i, X4 : $i]:
% 0.38/0.61         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.38/0.61          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ 
% 0.38/0.61             (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 0.38/0.61          | ((k1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.61              = (k10_relat_1 @ (k6_relat_1 @ X1) @ (k2_xboole_0 @ X1 @ X0)))
% 0.38/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['11', '14'])).
% 0.38/0.61  thf('16', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.61  thf(t7_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('17', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.61  thf('18', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 0.38/0.61           = (k2_xboole_0 @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.38/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf('20', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((X1) = (k2_xboole_0 @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0)))),
% 0.38/0.61      inference('demod', [status(thm)], ['15', '16', '17', '18', '19', '20'])).
% 0.38/0.61  thf('22', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['6', '21'])).
% 0.38/0.61  thf('23', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t9_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.61       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X10 @ X11)
% 0.38/0.61          | (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ (k2_xboole_0 @ X11 @ X12)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (r1_tarski @ (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0) @ 
% 0.38/0.61          (k2_xboole_0 @ sk_B @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      ((r1_tarski @ (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B) @ sk_B)),
% 0.38/0.61      inference('sup+', [status(thm)], ['22', '25'])).
% 0.38/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      ((r1_tarski @ (k2_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X2 : $i, X4 : $i]:
% 0.38/0.61         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.38/0.61          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (((k2_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['28', '31'])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.38/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.61  thf('34', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.38/0.61      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.61         (((k10_relat_1 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.38/0.61            = (k2_xboole_0 @ (k10_relat_1 @ X16 @ X17) @ 
% 0.38/0.61               (k10_relat_1 @ X16 @ X18)))
% 0.38/0.61          | ~ (v1_relat_1 @ X16))),
% 0.38/0.61      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.38/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.61  thf('38', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t146_funct_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ B ) =>
% 0.38/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.61         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 0.38/0.61          | (r1_tarski @ X23 @ (k10_relat_1 @ X24 @ (k9_relat_1 @ X24 @ X23)))
% 0.38/0.61          | ~ (v1_relat_1 @ X24))),
% 0.38/0.61      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.61  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['40', '41'])).
% 0.38/0.61  thf(t1_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.38/0.61       ( r1_tarski @ A @ C ) ))).
% 0.38/0.61  thf('43', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.61          | ~ (r1_tarski @ X6 @ X7)
% 0.38/0.61          | (r1_tarski @ X5 @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_A @ X0)
% 0.38/0.61          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.38/0.61               X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (r1_tarski @ sk_A @ 
% 0.38/0.61          (k2_xboole_0 @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['37', '44'])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.61         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.61          | ~ (r1_tarski @ X6 @ X7)
% 0.38/0.61          | (r1_tarski @ X5 @ X7))),
% 0.38/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r1_tarski @ sk_A @ X1)
% 0.38/0.61          | ~ (r1_tarski @ 
% 0.38/0.61               (k2_xboole_0 @ 
% 0.38/0.61                (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ X0) @ 
% 0.38/0.61               X1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ 
% 0.38/0.61             (k2_xboole_0 @ X0 @ 
% 0.38/0.61              (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))) @ 
% 0.38/0.61             X1)
% 0.38/0.61          | (r1_tarski @ sk_A @ X1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['36', '47'])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ 
% 0.38/0.61             (k10_relat_1 @ sk_C @ 
% 0.38/0.61              (k2_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A))) @ 
% 0.38/0.61             X1)
% 0.38/0.61          | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61          | (r1_tarski @ sk_A @ X1))),
% 0.38/0.61      inference('sup-', [status(thm)], ['35', '48'])).
% 0.38/0.61  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         (~ (r1_tarski @ 
% 0.38/0.61             (k10_relat_1 @ sk_C @ 
% 0.38/0.61              (k2_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A))) @ 
% 0.38/0.61             X1)
% 0.38/0.61          | (r1_tarski @ sk_A @ X1))),
% 0.38/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (r1_tarski @ sk_A @ 
% 0.38/0.61          (k10_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['34', '51'])).
% 0.38/0.61  thf('53', plain, ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['32', '52'])).
% 0.38/0.61  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
