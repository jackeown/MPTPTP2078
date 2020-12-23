%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91PEP4Lbyr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:06 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 106 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  582 (1008 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( r1_tarski @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k2_relat_1 @ X18 ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X27 )
        = ( k3_xboole_0 @ X25 @ ( k10_relat_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k10_relat_1 @ X19 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( r1_tarski @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X29 ) ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.91PEP4Lbyr
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 249 iterations in 0.215s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.67  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.67  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.67  thf(t152_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ( v2_funct_1 @ B ) =>
% 0.47/0.67         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.47/0.67  thf('0', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X28)
% 0.47/0.67          | (r1_tarski @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X29)) @ X29)
% 0.47/0.67          | ~ (v1_funct_1 @ X28)
% 0.47/0.67          | ~ (v1_relat_1 @ X28))),
% 0.47/0.67      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.47/0.67  thf(t28_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X6 : $i, X7 : $i]:
% 0.47/0.67         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.47/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | ~ (v2_funct_1 @ X1)
% 0.47/0.67          | ((k3_xboole_0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 0.47/0.67              = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.67  thf(commutativity_k2_tarski, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.47/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.47/0.67  thf(t12_setfam_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i]:
% 0.47/0.67         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.67      inference('sup+', [status(thm)], ['5', '6'])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | ~ (v2_funct_1 @ X1)
% 0.47/0.67          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.47/0.67              = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.47/0.67      inference('demod', [status(thm)], ['2', '7'])).
% 0.47/0.67  thf(t139_funct_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ C ) =>
% 0.47/0.67       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.47/0.67         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.47/0.67            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.47/0.67          | ~ (v1_relat_1 @ X26))),
% 0.47/0.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.67  thf(t148_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X14 : $i, X15 : $i]:
% 0.47/0.67         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.47/0.67          | ~ (v1_relat_1 @ X14))),
% 0.47/0.67      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.67  thf(t169_relat_1, axiom,
% 0.47/0.67    (![A:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) =>
% 0.47/0.67       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X18 : $i]:
% 0.47/0.67         (((k10_relat_1 @ X18 @ (k2_relat_1 @ X18)) = (k1_relat_1 @ X18))
% 0.47/0.67          | ~ (v1_relat_1 @ X18))),
% 0.47/0.67      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.47/0.67  thf(t170_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ B ) =>
% 0.47/0.67       ( r1_tarski @
% 0.47/0.67         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X19 : $i, X20 : $i]:
% 0.47/0.67         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ 
% 0.47/0.67           (k10_relat_1 @ X19 @ (k2_relat_1 @ X19)))
% 0.47/0.67          | ~ (v1_relat_1 @ X19))),
% 0.47/0.67      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.47/0.67           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.47/0.67          | ~ (v1_relat_1 @ X0)
% 0.47/0.67          | ~ (v1_relat_1 @ X0))),
% 0.47/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X0)
% 0.47/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.47/0.67             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.47/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.47/0.67  thf(t164_funct_1, conjecture,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.47/0.67         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i]:
% 0.47/0.67        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.67          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.47/0.67            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.47/0.67  thf('15', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(t1_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.67       ( r1_tarski @ A @ C ) ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X3 @ X4)
% 0.47/0.67          | ~ (r1_tarski @ X4 @ X5)
% 0.47/0.67          | (r1_tarski @ X3 @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.47/0.67        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['14', '17'])).
% 0.47/0.67  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.47/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      (![X6 : $i, X7 : $i]:
% 0.47/0.67         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.47/0.67      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.47/0.67         = (sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.47/0.67         (((k10_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X27)
% 0.47/0.67            = (k3_xboole_0 @ X25 @ (k10_relat_1 @ X26 @ X27)))
% 0.47/0.67          | ~ (v1_relat_1 @ X26))),
% 0.47/0.67      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X19 : $i, X20 : $i]:
% 0.47/0.67         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ 
% 0.47/0.67           (k10_relat_1 @ X19 @ (k2_relat_1 @ X19)))
% 0.47/0.67          | ~ (v1_relat_1 @ X19))),
% 0.47/0.67      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.47/0.67           (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 0.47/0.67            (k2_relat_1 @ (k7_relat_1 @ X1 @ X2))))
% 0.47/0.67          | ~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.47/0.67      inference('sup+', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf(dt_k7_relat_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.47/0.67  thf('26', plain,
% 0.47/0.67      (![X12 : $i, X13 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.47/0.67             (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 0.47/0.67              (k2_relat_1 @ (k7_relat_1 @ X1 @ X2)))))),
% 0.47/0.67      inference('clc', [status(thm)], ['25', '26'])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (((r1_tarski @ sk_A @ 
% 0.47/0.67         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.67          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['22', '27'])).
% 0.47/0.67  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((r1_tarski @ sk_A @ 
% 0.47/0.67        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.67         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      (((r1_tarski @ sk_A @ 
% 0.47/0.67         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['10', '30'])).
% 0.47/0.67  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      ((r1_tarski @ sk_A @ 
% 0.47/0.67        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['31', '32'])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (((r1_tarski @ sk_A @ 
% 0.47/0.67         (k3_xboole_0 @ sk_A @ 
% 0.47/0.67          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['9', '33'])).
% 0.47/0.67  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      ((r1_tarski @ sk_A @ 
% 0.47/0.67        (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_B)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['8', '36'])).
% 0.47/0.67  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X28 : $i, X29 : $i]:
% 0.47/0.67         (~ (v2_funct_1 @ X28)
% 0.47/0.67          | (r1_tarski @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X29)) @ X29)
% 0.47/0.67          | ~ (v1_funct_1 @ X28)
% 0.47/0.67          | ~ (v1_relat_1 @ X28))),
% 0.47/0.67      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('43', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (v1_relat_1 @ X1)
% 0.47/0.67          | ~ (v1_funct_1 @ X1)
% 0.47/0.67          | ~ (v2_funct_1 @ X1)
% 0.47/0.67          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.47/0.67          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      ((((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.67        | ~ (v2_funct_1 @ sk_B)
% 0.47/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.47/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['41', '44'])).
% 0.47/0.67  thf('46', plain, ((v2_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (((sk_A) = (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.67      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('51', plain, ($false),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['49', '50'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
