%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PPjWN69KLV

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 152 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   20
%              Number of atoms          :  606 (1277 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k3_xboole_0 @ X37 @ ( k10_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) )
        = ( k9_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X35 ) @ X36 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('22',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k3_xboole_0 @ X37 @ ( k10_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X29 @ X30 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('47',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PPjWN69KLV
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.50/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.70  % Solved by: fo/fo7.sh
% 1.50/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.70  % done 3212 iterations in 1.245s
% 1.50/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.70  % SZS output start Refutation
% 1.50/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.50/1.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.50/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.50/1.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.50/1.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.50/1.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.50/1.70  thf(t146_funct_1, conjecture,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.50/1.70         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.50/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.70    (~( ![A:$i,B:$i]:
% 1.50/1.70        ( ( v1_relat_1 @ B ) =>
% 1.50/1.70          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.50/1.70            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.50/1.70    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.50/1.70  thf('0', plain,
% 1.50/1.70      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf(t139_funct_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ C ) =>
% 1.50/1.70       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.50/1.70         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.50/1.70  thf('1', plain,
% 1.50/1.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.70         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 1.50/1.70            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 1.50/1.70          | ~ (v1_relat_1 @ X38))),
% 1.50/1.70      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.50/1.70  thf(t148_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.50/1.70  thf('2', plain,
% 1.50/1.70      (![X27 : $i, X28 : $i]:
% 1.50/1.70         (((k2_relat_1 @ (k7_relat_1 @ X27 @ X28)) = (k9_relat_1 @ X27 @ X28))
% 1.50/1.70          | ~ (v1_relat_1 @ X27))),
% 1.50/1.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.50/1.70  thf(t169_relat_1, axiom,
% 1.50/1.70    (![A:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ A ) =>
% 1.50/1.70       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.50/1.70  thf('3', plain,
% 1.50/1.70      (![X31 : $i]:
% 1.50/1.70         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 1.50/1.70          | ~ (v1_relat_1 @ X31))),
% 1.50/1.70      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.70  thf('4', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.50/1.70            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.70          | ~ (v1_relat_1 @ X1)
% 1.50/1.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.50/1.70      inference('sup+', [status(thm)], ['2', '3'])).
% 1.50/1.70  thf(dt_k7_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.50/1.70  thf('5', plain,
% 1.50/1.70      (![X25 : $i, X26 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.70  thf('6', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.50/1.70              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.70      inference('clc', [status(thm)], ['4', '5'])).
% 1.50/1.70  thf('7', plain,
% 1.50/1.70      (![X25 : $i, X26 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.70  thf(d10_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.70  thf('8', plain,
% 1.50/1.70      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.50/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.70  thf('9', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.70      inference('simplify', [status(thm)], ['8'])).
% 1.50/1.70  thf('10', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf(t19_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.50/1.70       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.50/1.70  thf('11', plain,
% 1.50/1.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X15 @ X16)
% 1.50/1.70          | ~ (r1_tarski @ X15 @ X17)
% 1.50/1.70          | (r1_tarski @ X15 @ (k3_xboole_0 @ X16 @ X17)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.50/1.70  thf('12', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         ((r1_tarski @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))
% 1.50/1.70          | ~ (r1_tarski @ sk_A @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['10', '11'])).
% 1.50/1.70  thf('13', plain,
% 1.50/1.70      ((r1_tarski @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 1.50/1.70      inference('sup-', [status(thm)], ['9', '12'])).
% 1.50/1.70  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.70  thf('14', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('15', plain,
% 1.50/1.70      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.50/1.70      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.70  thf(t17_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.50/1.70  thf('16', plain,
% 1.50/1.70      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf('17', plain,
% 1.50/1.70      (![X2 : $i, X4 : $i]:
% 1.50/1.70         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.50/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.70  thf('18', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.70          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['16', '17'])).
% 1.50/1.70  thf('19', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['15', '18'])).
% 1.50/1.70  thf('20', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf(t90_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 1.50/1.70         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.50/1.70  thf('21', plain,
% 1.50/1.70      (![X35 : $i, X36 : $i]:
% 1.50/1.70         (((k1_relat_1 @ (k7_relat_1 @ X35 @ X36))
% 1.50/1.70            = (k3_xboole_0 @ (k1_relat_1 @ X35) @ X36))
% 1.50/1.70          | ~ (v1_relat_1 @ X35))),
% 1.50/1.70      inference('cnf', [status(esa)], [t90_relat_1])).
% 1.50/1.70  thf('22', plain,
% 1.50/1.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.50/1.70         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 1.50/1.70            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 1.50/1.70          | ~ (v1_relat_1 @ X38))),
% 1.50/1.70      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.50/1.70  thf('23', plain,
% 1.50/1.70      (![X31 : $i]:
% 1.50/1.70         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 1.50/1.70          | ~ (v1_relat_1 @ X31))),
% 1.50/1.70      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.70  thf('24', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (((k3_xboole_0 @ X0 @ 
% 1.50/1.70            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.50/1.70            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.70          | ~ (v1_relat_1 @ X1)
% 1.50/1.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.50/1.70      inference('sup+', [status(thm)], ['22', '23'])).
% 1.50/1.70  thf('25', plain,
% 1.50/1.70      (![X25 : $i, X26 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X25) | (v1_relat_1 @ (k7_relat_1 @ X25 @ X26)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.50/1.70  thf('26', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | ((k3_xboole_0 @ X0 @ 
% 1.50/1.70              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.50/1.70              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.70      inference('clc', [status(thm)], ['24', '25'])).
% 1.50/1.70  thf('27', plain,
% 1.50/1.70      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf('28', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ X1))),
% 1.50/1.70      inference('sup+', [status(thm)], ['26', '27'])).
% 1.50/1.70  thf('29', plain,
% 1.50/1.70      (![X2 : $i, X4 : $i]:
% 1.50/1.70         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.50/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.70  thf('30', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.70          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.50/1.70      inference('sup-', [status(thm)], ['28', '29'])).
% 1.50/1.70  thf('31', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 1.50/1.70          | ~ (v1_relat_1 @ X1)
% 1.50/1.70          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.70          | ~ (v1_relat_1 @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['21', '30'])).
% 1.50/1.70  thf('32', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.50/1.70          | ~ (v1_relat_1 @ X1)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 1.50/1.70      inference('simplify', [status(thm)], ['31'])).
% 1.50/1.70  thf('33', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X1 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 1.50/1.70          | ~ (v1_relat_1 @ X0)
% 1.50/1.70          | ((X1) = (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 1.50/1.70      inference('sup-', [status(thm)], ['20', '32'])).
% 1.50/1.70  thf('34', plain,
% 1.50/1.70      ((~ (r1_tarski @ sk_A @ sk_A)
% 1.50/1.70        | ((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.50/1.70        | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.70      inference('sup-', [status(thm)], ['19', '33'])).
% 1.50/1.70  thf('35', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.70      inference('simplify', [status(thm)], ['8'])).
% 1.50/1.70  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('37', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.50/1.70  thf(t167_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.50/1.70  thf('38', plain,
% 1.50/1.70      (![X29 : $i, X30 : $i]:
% 1.50/1.70         ((r1_tarski @ (k10_relat_1 @ X29 @ X30) @ (k1_relat_1 @ X29))
% 1.50/1.70          | ~ (v1_relat_1 @ X29))),
% 1.50/1.70      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.50/1.70  thf('39', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 1.50/1.70          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('sup+', [status(thm)], ['37', '38'])).
% 1.50/1.70  thf('40', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ sk_B)
% 1.50/1.70          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 1.50/1.70      inference('sup-', [status(thm)], ['7', '39'])).
% 1.50/1.70  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('42', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 1.50/1.70      inference('demod', [status(thm)], ['40', '41'])).
% 1.50/1.70  thf('43', plain,
% 1.50/1.70      (![X2 : $i, X4 : $i]:
% 1.50/1.70         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.50/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.70  thf('44', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 1.50/1.70          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['42', '43'])).
% 1.50/1.70  thf('45', plain,
% 1.50/1.70      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.50/1.70        | ~ (v1_relat_1 @ sk_B)
% 1.50/1.70        | ((sk_A)
% 1.50/1.70            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.50/1.70               (k9_relat_1 @ sk_B @ sk_A))))),
% 1.50/1.70      inference('sup-', [status(thm)], ['6', '44'])).
% 1.50/1.70  thf('46', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.50/1.70  thf('47', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.70      inference('simplify', [status(thm)], ['8'])).
% 1.50/1.70  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('49', plain,
% 1.50/1.70      (((sk_A)
% 1.50/1.70         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.50/1.70            (k9_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 1.50/1.70  thf('50', plain,
% 1.50/1.70      ((((sk_A)
% 1.50/1.70          = (k3_xboole_0 @ sk_A @ 
% 1.50/1.70             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 1.50/1.70        | ~ (v1_relat_1 @ sk_B))),
% 1.50/1.70      inference('sup+', [status(thm)], ['1', '49'])).
% 1.50/1.70  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('52', plain,
% 1.50/1.70      (((sk_A)
% 1.50/1.70         = (k3_xboole_0 @ sk_A @ 
% 1.50/1.70            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.50/1.70      inference('demod', [status(thm)], ['50', '51'])).
% 1.50/1.70  thf('53', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.70  thf('54', plain,
% 1.50/1.70      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 1.50/1.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.50/1.70  thf('55', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.50/1.70      inference('sup+', [status(thm)], ['53', '54'])).
% 1.50/1.70  thf('56', plain,
% 1.50/1.70      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.50/1.70      inference('sup+', [status(thm)], ['52', '55'])).
% 1.50/1.70  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 1.50/1.70  
% 1.50/1.70  % SZS output end Refutation
% 1.50/1.70  
% 1.50/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
