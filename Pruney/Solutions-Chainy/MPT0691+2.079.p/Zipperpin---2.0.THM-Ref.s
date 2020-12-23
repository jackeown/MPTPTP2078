%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJ2HezOncM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:29 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 133 expanded)
%              Number of leaves         :   19 (  45 expanded)
%              Depth                    :   18
%              Number of atoms          :  645 (1199 expanded)
%              Number of equality atoms :   46 (  61 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k3_xboole_0 @ X15 @ ( k10_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('10',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('22',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('24',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('25',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('29',plain,(
    ! [X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X10 ) @ X11 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NJ2HezOncM
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 194 iterations in 0.161s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(t146_funct_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.62         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( v1_relat_1 @ B ) =>
% 0.41/0.62          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.62            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t139_funct_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ C ) =>
% 0.41/0.62       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.41/0.62         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.62         (((k10_relat_1 @ (k7_relat_1 @ X16 @ X15) @ X17)
% 0.41/0.62            = (k3_xboole_0 @ X15 @ (k10_relat_1 @ X16 @ X17)))
% 0.41/0.62          | ~ (v1_relat_1 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.41/0.62  thf(t148_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]:
% 0.41/0.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.41/0.62          | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.62  thf(dt_k7_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.62  thf('4', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t91_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.62         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 0.41/0.62          | ((k1_relat_1 @ (k7_relat_1 @ X13 @ X12)) = (X12))
% 0.41/0.62          | ~ (v1_relat_1 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('8', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf(t98_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X14 : $i]:
% 0.41/0.62         (((k7_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (X14))
% 0.41/0.62          | ~ (v1_relat_1 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X14 : $i]:
% 0.41/0.62         (((k7_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (X14))
% 0.41/0.62          | ~ (v1_relat_1 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]:
% 0.41/0.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.41/0.62          | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.62  thf(t169_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X7 : $i]:
% 0.41/0.62         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 0.41/0.62          | ~ (v1_relat_1 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.62            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.41/0.62          | ~ (v1_relat_1 @ X1)
% 0.41/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X1)
% 0.41/0.62          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.41/0.62              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.41/0.62      inference('clc', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.41/0.62            = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.41/0.62              = (k1_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.41/0.62            = (k1_relat_1 @ X0))
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['9', '17'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.41/0.62              = (k1_relat_1 @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.62          (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))
% 0.41/0.62          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.41/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '19'])).
% 0.41/0.62  thf('21', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.62          (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)) = (sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf(t90_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.41/0.62         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i]:
% 0.41/0.62         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 0.41/0.62            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 0.41/0.62          | ~ (v1_relat_1 @ X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.41/0.62  thf('24', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('27', plain, (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['25', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i]:
% 0.41/0.62         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 0.41/0.62            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 0.41/0.62          | ~ (v1_relat_1 @ X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X14 : $i]:
% 0.41/0.62         (((k7_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (X14))
% 0.41/0.62          | ~ (v1_relat_1 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X5 : $i, X6 : $i]:
% 0.41/0.62         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.41/0.62          | ~ (v1_relat_1 @ X5))),
% 0.41/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.41/0.62          | ~ (v1_relat_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X0)
% 0.41/0.62          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.41/0.62            = (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.41/0.62               (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.41/0.62          | ~ (v1_relat_1 @ X1)
% 0.41/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['28', '32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X1)
% 0.41/0.62          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.41/0.62              = (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.41/0.62                 (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.41/0.62      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.41/0.62          = (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['27', '35'])).
% 0.41/0.62  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.41/0.62         = (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.62          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['22', '38'])).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_B)
% 0.41/0.62        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.62            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '39'])).
% 0.41/0.62  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.41/0.62         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.62          = (sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['2', '42'])).
% 0.41/0.62  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.41/0.62         = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      ((((k3_xboole_0 @ sk_A @ 
% 0.41/0.62          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['1', '45'])).
% 0.41/0.62  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.41/0.62         = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.41/0.62  thf('50', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i]:
% 0.41/0.62         (((k1_relat_1 @ (k7_relat_1 @ X10 @ X11))
% 0.41/0.62            = (k3_xboole_0 @ (k1_relat_1 @ X10) @ X11))
% 0.41/0.62          | ~ (v1_relat_1 @ X10))),
% 0.41/0.62      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.41/0.62  thf(t87_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ B ) =>
% 0.41/0.62       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i]:
% 0.41/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.41/0.62          | ~ (v1_relat_1 @ X8))),
% 0.41/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X1)
% 0.41/0.62          | ~ (v1_relat_1 @ X1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ X1)
% 0.41/0.62          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['50', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '55'])).
% 0.41/0.62  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('58', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)),
% 0.41/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['48', '58'])).
% 0.41/0.62  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
