%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NogEfh6vDH

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:20 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 193 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :   23
%              Number of atoms          :  695 (1683 expanded)
%              Number of equality atoms :   36 (  69 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k10_relat_1 @ sk_B @ X0 ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','25','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','35'])).

thf('37',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k3_xboole_0 @ X28 @ ( k10_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('38',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('58',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NogEfh6vDH
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.41  % Solved by: fo/fo7.sh
% 1.19/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.41  % done 2508 iterations in 0.954s
% 1.19/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.41  % SZS output start Refutation
% 1.19/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.41  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.19/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.41  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.19/1.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.41  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.19/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.41  thf(t146_funct_1, conjecture,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ B ) =>
% 1.19/1.41       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.19/1.41         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.19/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.41    (~( ![A:$i,B:$i]:
% 1.19/1.41        ( ( v1_relat_1 @ B ) =>
% 1.19/1.41          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.19/1.41            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 1.19/1.41    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 1.19/1.41  thf('0', plain,
% 1.19/1.41      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t139_funct_1, axiom,
% 1.19/1.41    (![A:$i,B:$i,C:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ C ) =>
% 1.19/1.41       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.19/1.41         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.19/1.41  thf('1', plain,
% 1.19/1.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.19/1.41         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 1.19/1.41            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 1.19/1.41          | ~ (v1_relat_1 @ X29))),
% 1.19/1.41      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.19/1.41  thf(t148_relat_1, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ B ) =>
% 1.19/1.41       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.19/1.41  thf('2', plain,
% 1.19/1.41      (![X23 : $i, X24 : $i]:
% 1.19/1.41         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 1.19/1.41          | ~ (v1_relat_1 @ X23))),
% 1.19/1.41      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.19/1.41  thf(t169_relat_1, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ A ) =>
% 1.19/1.41       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.19/1.41  thf('3', plain,
% 1.19/1.41      (![X27 : $i]:
% 1.19/1.41         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.19/1.41          | ~ (v1_relat_1 @ X27))),
% 1.19/1.41      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.19/1.41  thf('4', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.19/1.41            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.19/1.41          | ~ (v1_relat_1 @ X1)
% 1.19/1.41          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['2', '3'])).
% 1.19/1.41  thf(dt_k7_relat_1, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.19/1.41  thf('5', plain,
% 1.19/1.41      (![X21 : $i, X22 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 1.19/1.41      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.19/1.41  thf('6', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X1)
% 1.19/1.41          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 1.19/1.41              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.19/1.41      inference('clc', [status(thm)], ['4', '5'])).
% 1.19/1.41  thf('7', plain,
% 1.19/1.41      (![X21 : $i, X22 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 1.19/1.41      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.19/1.41  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t28_xboole_1, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.19/1.41  thf('9', plain,
% 1.19/1.41      (![X16 : $i, X17 : $i]:
% 1.19/1.41         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.19/1.41      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.19/1.41  thf('10', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['8', '9'])).
% 1.19/1.41  thf('11', plain,
% 1.19/1.41      (![X27 : $i]:
% 1.19/1.41         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.19/1.41          | ~ (v1_relat_1 @ X27))),
% 1.19/1.41      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.19/1.41  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t167_relat_1, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( v1_relat_1 @ B ) =>
% 1.19/1.41       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.19/1.41  thf('13', plain,
% 1.19/1.41      (![X25 : $i, X26 : $i]:
% 1.19/1.41         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 1.19/1.41          | ~ (v1_relat_1 @ X25))),
% 1.19/1.41      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.19/1.41  thf(t8_xboole_1, axiom,
% 1.19/1.41    (![A:$i,B:$i,C:$i]:
% 1.19/1.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.19/1.41       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.19/1.41  thf('14', plain,
% 1.19/1.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.41         (~ (r1_tarski @ X18 @ X19)
% 1.19/1.41          | ~ (r1_tarski @ X20 @ X19)
% 1.19/1.41          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 1.19/1.41      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.19/1.41  thf('15', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X0)
% 1.19/1.41          | (r1_tarski @ (k2_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 1.19/1.41             (k1_relat_1 @ X0))
% 1.19/1.41          | ~ (r1_tarski @ X2 @ (k1_relat_1 @ X0)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['13', '14'])).
% 1.19/1.41  thf('16', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         ((r1_tarski @ (k2_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ sk_A) @ 
% 1.19/1.41           (k1_relat_1 @ sk_B))
% 1.19/1.41          | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.41      inference('sup-', [status(thm)], ['12', '15'])).
% 1.19/1.41  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('18', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (r1_tarski @ (k2_xboole_0 @ (k10_relat_1 @ sk_B @ X0) @ sk_A) @ 
% 1.19/1.41          (k1_relat_1 @ sk_B))),
% 1.19/1.41      inference('demod', [status(thm)], ['16', '17'])).
% 1.19/1.41  thf(t11_xboole_1, axiom,
% 1.19/1.41    (![A:$i,B:$i,C:$i]:
% 1.19/1.41     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.19/1.41  thf('19', plain,
% 1.19/1.41      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.41         ((r1_tarski @ X9 @ X10)
% 1.19/1.41          | ~ (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 1.19/1.41      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.19/1.41  thf('20', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 1.19/1.41      inference('sup-', [status(thm)], ['18', '19'])).
% 1.19/1.41  thf(d10_xboole_0, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.19/1.41  thf('21', plain,
% 1.19/1.41      (![X6 : $i, X8 : $i]:
% 1.19/1.41         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.19/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.41  thf('22', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 1.19/1.41          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['20', '21'])).
% 1.19/1.41  thf('23', plain,
% 1.19/1.41      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 1.19/1.41        | ~ (v1_relat_1 @ sk_B)
% 1.19/1.41        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 1.19/1.41      inference('sup-', [status(thm)], ['11', '22'])).
% 1.19/1.41  thf('24', plain,
% 1.19/1.41      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 1.19/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.41  thf('25', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.19/1.41      inference('simplify', [status(thm)], ['24'])).
% 1.19/1.41  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('27', plain,
% 1.19/1.41      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 1.19/1.41      inference('demod', [status(thm)], ['23', '25', '26'])).
% 1.19/1.41  thf('28', plain,
% 1.19/1.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.19/1.41         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 1.19/1.41            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 1.19/1.41          | ~ (v1_relat_1 @ X29))),
% 1.19/1.41      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.19/1.41  thf('29', plain,
% 1.19/1.41      (![X25 : $i, X26 : $i]:
% 1.19/1.41         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 1.19/1.41          | ~ (v1_relat_1 @ X25))),
% 1.19/1.41      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.19/1.41  thf('30', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.41         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.19/1.41           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 1.19/1.41          | ~ (v1_relat_1 @ X1)
% 1.19/1.41          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['28', '29'])).
% 1.19/1.41  thf('31', plain,
% 1.19/1.41      (![X21 : $i, X22 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 1.19/1.41      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.19/1.41  thf('32', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X1)
% 1.19/1.41          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 1.19/1.41             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 1.19/1.41      inference('clc', [status(thm)], ['30', '31'])).
% 1.19/1.41  thf('33', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.19/1.41           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 1.19/1.41          | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.41      inference('sup+', [status(thm)], ['27', '32'])).
% 1.19/1.41  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('35', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 1.19/1.41          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 1.19/1.41      inference('demod', [status(thm)], ['33', '34'])).
% 1.19/1.41  thf('36', plain,
% 1.19/1.41      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['10', '35'])).
% 1.19/1.41  thf('37', plain,
% 1.19/1.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.19/1.41         (((k10_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X30)
% 1.19/1.41            = (k3_xboole_0 @ X28 @ (k10_relat_1 @ X29 @ X30)))
% 1.19/1.41          | ~ (v1_relat_1 @ X29))),
% 1.19/1.41      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.19/1.41  thf('38', plain,
% 1.19/1.41      (![X27 : $i]:
% 1.19/1.41         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.19/1.41          | ~ (v1_relat_1 @ X27))),
% 1.19/1.41      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.19/1.41  thf('39', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (((k3_xboole_0 @ X0 @ 
% 1.19/1.41            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.19/1.41            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.19/1.41          | ~ (v1_relat_1 @ X1)
% 1.19/1.41          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['37', '38'])).
% 1.19/1.41  thf('40', plain,
% 1.19/1.41      (![X21 : $i, X22 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 1.19/1.41      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.19/1.41  thf('41', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X1)
% 1.19/1.41          | ((k3_xboole_0 @ X0 @ 
% 1.19/1.41              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 1.19/1.41              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.19/1.41      inference('clc', [status(thm)], ['39', '40'])).
% 1.19/1.41  thf(t17_xboole_1, axiom,
% 1.19/1.41    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.41  thf('42', plain,
% 1.19/1.41      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 1.19/1.41      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.41  thf('43', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.19/1.41          | ~ (v1_relat_1 @ X1))),
% 1.19/1.41      inference('sup+', [status(thm)], ['41', '42'])).
% 1.19/1.41  thf('44', plain,
% 1.19/1.41      (![X6 : $i, X8 : $i]:
% 1.19/1.41         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.19/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.41  thf('45', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ X1)
% 1.19/1.41          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.19/1.41          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 1.19/1.41      inference('sup-', [status(thm)], ['43', '44'])).
% 1.19/1.41  thf('46', plain,
% 1.19/1.41      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.19/1.41        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.41      inference('sup-', [status(thm)], ['36', '45'])).
% 1.19/1.41  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('48', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('demod', [status(thm)], ['46', '47'])).
% 1.19/1.41  thf('49', plain,
% 1.19/1.41      (![X25 : $i, X26 : $i]:
% 1.19/1.41         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 1.19/1.41          | ~ (v1_relat_1 @ X25))),
% 1.19/1.41      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.19/1.41  thf('50', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 1.19/1.41          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['48', '49'])).
% 1.19/1.41  thf('51', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (~ (v1_relat_1 @ sk_B)
% 1.19/1.41          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['7', '50'])).
% 1.19/1.41  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('53', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 1.19/1.41      inference('demod', [status(thm)], ['51', '52'])).
% 1.19/1.41  thf('54', plain,
% 1.19/1.41      (![X6 : $i, X8 : $i]:
% 1.19/1.41         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 1.19/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.19/1.41  thf('55', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 1.19/1.41          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.19/1.41  thf('56', plain,
% 1.19/1.41      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 1.19/1.41        | ~ (v1_relat_1 @ sk_B)
% 1.19/1.41        | ((sk_A)
% 1.19/1.41            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.19/1.41               (k9_relat_1 @ sk_B @ sk_A))))),
% 1.19/1.41      inference('sup-', [status(thm)], ['6', '55'])).
% 1.19/1.41  thf('57', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('demod', [status(thm)], ['46', '47'])).
% 1.19/1.41  thf('58', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 1.19/1.41      inference('simplify', [status(thm)], ['24'])).
% 1.19/1.41  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('60', plain,
% 1.19/1.41      (((sk_A)
% 1.19/1.41         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 1.19/1.41            (k9_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 1.19/1.41  thf('61', plain,
% 1.19/1.41      ((((sk_A)
% 1.19/1.41          = (k3_xboole_0 @ sk_A @ 
% 1.19/1.41             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 1.19/1.41        | ~ (v1_relat_1 @ sk_B))),
% 1.19/1.41      inference('sup+', [status(thm)], ['1', '60'])).
% 1.19/1.41  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('63', plain,
% 1.19/1.41      (((sk_A)
% 1.19/1.41         = (k3_xboole_0 @ sk_A @ 
% 1.19/1.41            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 1.19/1.41      inference('demod', [status(thm)], ['61', '62'])).
% 1.19/1.41  thf(commutativity_k3_xboole_0, axiom,
% 1.19/1.41    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.19/1.41  thf('64', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.19/1.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.19/1.41  thf('65', plain,
% 1.19/1.41      (![X14 : $i, X15 : $i]: (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ X14)),
% 1.19/1.41      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.19/1.41  thf('66', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.19/1.41      inference('sup+', [status(thm)], ['64', '65'])).
% 1.19/1.41  thf('67', plain,
% 1.19/1.41      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['63', '66'])).
% 1.19/1.41  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 1.19/1.41  
% 1.19/1.41  % SZS output end Refutation
% 1.19/1.41  
% 1.25/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
