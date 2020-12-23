%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lvjZd4qigL

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:17 EST 2020

% Result     : Theorem 6.00s
% Output     : Refutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 205 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   23
%              Number of atoms          :  926 (1705 expanded)
%              Number of equality atoms :   47 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k3_xboole_0 @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k3_xboole_0 @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('40',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k3_xboole_0 @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('47',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('61',plain,(
    ! [X31: $i] :
      ( ( ( k10_relat_1 @ X31 @ ( k2_relat_1 @ X31 ) )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k9_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X32 @ X33 ) @ ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['38','74'])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lvjZd4qigL
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:48:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.00/6.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.00/6.18  % Solved by: fo/fo7.sh
% 6.00/6.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.00/6.18  % done 11444 iterations in 5.722s
% 6.00/6.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.00/6.18  % SZS output start Refutation
% 6.00/6.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.00/6.18  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.00/6.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.00/6.18  thf(sk_A_type, type, sk_A: $i).
% 6.00/6.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.00/6.18  thf(sk_B_type, type, sk_B: $i).
% 6.00/6.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.00/6.18  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.00/6.18  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.00/6.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.00/6.18  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.00/6.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.00/6.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.00/6.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.00/6.18  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 6.00/6.18  thf(t146_funct_1, conjecture,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ B ) =>
% 6.00/6.18       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 6.00/6.18         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 6.00/6.18  thf(zf_stmt_0, negated_conjecture,
% 6.00/6.18    (~( ![A:$i,B:$i]:
% 6.00/6.18        ( ( v1_relat_1 @ B ) =>
% 6.00/6.18          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 6.00/6.18            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 6.00/6.18    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 6.00/6.18  thf('0', plain,
% 6.00/6.18      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf(t139_funct_1, axiom,
% 6.00/6.18    (![A:$i,B:$i,C:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ C ) =>
% 6.00/6.18       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 6.00/6.18         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 6.00/6.18  thf('1', plain,
% 6.00/6.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.00/6.18         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 6.00/6.18            = (k3_xboole_0 @ X34 @ (k10_relat_1 @ X35 @ X36)))
% 6.00/6.18          | ~ (v1_relat_1 @ X35))),
% 6.00/6.18      inference('cnf', [status(esa)], [t139_funct_1])).
% 6.00/6.18  thf(t148_relat_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ B ) =>
% 6.00/6.18       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.00/6.18  thf('2', plain,
% 6.00/6.18      (![X29 : $i, X30 : $i]:
% 6.00/6.18         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 6.00/6.18          | ~ (v1_relat_1 @ X29))),
% 6.00/6.18      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.00/6.18  thf(d10_xboole_0, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.00/6.18  thf('3', plain,
% 6.00/6.18      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 6.00/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.00/6.18  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 6.00/6.18      inference('simplify', [status(thm)], ['3'])).
% 6.00/6.18  thf(t11_xboole_1, axiom,
% 6.00/6.18    (![A:$i,B:$i,C:$i]:
% 6.00/6.18     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 6.00/6.18  thf('5', plain,
% 6.00/6.18      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.00/6.18         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 6.00/6.18      inference('cnf', [status(esa)], [t11_xboole_1])).
% 6.00/6.18  thf('6', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 6.00/6.18      inference('sup-', [status(thm)], ['4', '5'])).
% 6.00/6.18  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf(t12_xboole_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 6.00/6.18  thf('8', plain,
% 6.00/6.18      (![X8 : $i, X9 : $i]:
% 6.00/6.18         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 6.00/6.18      inference('cnf', [status(esa)], [t12_xboole_1])).
% 6.00/6.18  thf('9', plain,
% 6.00/6.18      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup-', [status(thm)], ['7', '8'])).
% 6.00/6.18  thf('10', plain,
% 6.00/6.18      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.00/6.18         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 6.00/6.18      inference('cnf', [status(esa)], [t11_xboole_1])).
% 6.00/6.18  thf('11', plain,
% 6.00/6.18      (![X0 : $i]:
% 6.00/6.18         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r1_tarski @ sk_A @ X0))),
% 6.00/6.18      inference('sup-', [status(thm)], ['9', '10'])).
% 6.00/6.18  thf('12', plain,
% 6.00/6.18      (![X0 : $i]:
% 6.00/6.18         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 6.00/6.18      inference('sup-', [status(thm)], ['6', '11'])).
% 6.00/6.18  thf(t43_xboole_1, axiom,
% 6.00/6.18    (![A:$i,B:$i,C:$i]:
% 6.00/6.18     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 6.00/6.18       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 6.00/6.18  thf('13', plain,
% 6.00/6.18      (![X15 : $i, X16 : $i, X17 : $i]:
% 6.00/6.18         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 6.00/6.18          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 6.00/6.18      inference('cnf', [status(esa)], [t43_xboole_1])).
% 6.00/6.18  thf('14', plain,
% 6.00/6.18      (![X0 : $i]:
% 6.00/6.18         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 6.00/6.18      inference('sup-', [status(thm)], ['12', '13'])).
% 6.00/6.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.00/6.18  thf('15', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 6.00/6.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.00/6.18  thf('16', plain,
% 6.00/6.18      (![X2 : $i, X4 : $i]:
% 6.00/6.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 6.00/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.00/6.18  thf('17', plain,
% 6.00/6.18      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 6.00/6.18      inference('sup-', [status(thm)], ['15', '16'])).
% 6.00/6.18  thf('18', plain,
% 6.00/6.18      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 6.00/6.18      inference('sup-', [status(thm)], ['14', '17'])).
% 6.00/6.18  thf(t48_xboole_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.00/6.18  thf('19', plain,
% 6.00/6.18      (![X21 : $i, X22 : $i]:
% 6.00/6.18         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 6.00/6.18           = (k3_xboole_0 @ X21 @ X22))),
% 6.00/6.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.00/6.18  thf('20', plain,
% 6.00/6.18      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 6.00/6.18         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['18', '19'])).
% 6.00/6.18  thf(t3_boole, axiom,
% 6.00/6.18    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.00/6.18  thf('21', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 6.00/6.18      inference('cnf', [status(esa)], [t3_boole])).
% 6.00/6.18  thf('22', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 6.00/6.18      inference('demod', [status(thm)], ['20', '21'])).
% 6.00/6.18  thf(t169_relat_1, axiom,
% 6.00/6.18    (![A:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ A ) =>
% 6.00/6.18       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 6.00/6.18  thf('23', plain,
% 6.00/6.18      (![X31 : $i]:
% 6.00/6.18         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 6.00/6.18          | ~ (v1_relat_1 @ X31))),
% 6.00/6.18      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.00/6.18  thf('24', plain,
% 6.00/6.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.00/6.18         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 6.00/6.18            = (k3_xboole_0 @ X34 @ (k10_relat_1 @ X35 @ X36)))
% 6.00/6.18          | ~ (v1_relat_1 @ X35))),
% 6.00/6.18      inference('cnf', [status(esa)], [t139_funct_1])).
% 6.00/6.18  thf(t170_relat_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ B ) =>
% 6.00/6.18       ( r1_tarski @
% 6.00/6.18         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 6.00/6.18  thf('25', plain,
% 6.00/6.18      (![X32 : $i, X33 : $i]:
% 6.00/6.18         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 6.00/6.18           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 6.00/6.18          | ~ (v1_relat_1 @ X32))),
% 6.00/6.18      inference('cnf', [status(esa)], [t170_relat_1])).
% 6.00/6.18  thf('26', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 6.00/6.18           (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 6.00/6.18            (k2_relat_1 @ (k7_relat_1 @ X1 @ X2))))
% 6.00/6.18          | ~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['24', '25'])).
% 6.00/6.18  thf(dt_k7_relat_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 6.00/6.18  thf('27', plain,
% 6.00/6.18      (![X27 : $i, X28 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k7_relat_1 @ X27 @ X28)))),
% 6.00/6.18      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.00/6.18  thf('28', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 6.00/6.18             (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 6.00/6.18              (k2_relat_1 @ (k7_relat_1 @ X1 @ X2)))))),
% 6.00/6.18      inference('clc', [status(thm)], ['26', '27'])).
% 6.00/6.18  thf('29', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 6.00/6.18           (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 6.00/6.18            (k2_relat_1 @ (k7_relat_1 @ X0 @ X1))))
% 6.00/6.18          | ~ (v1_relat_1 @ X0)
% 6.00/6.18          | ~ (v1_relat_1 @ X0))),
% 6.00/6.18      inference('sup+', [status(thm)], ['23', '28'])).
% 6.00/6.18  thf('30', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X0)
% 6.00/6.18          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 6.00/6.18             (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ 
% 6.00/6.18              (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)))))),
% 6.00/6.18      inference('simplify', [status(thm)], ['29'])).
% 6.00/6.18  thf('31', plain,
% 6.00/6.18      (((r1_tarski @ sk_A @ 
% 6.00/6.18         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 6.00/6.18          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 6.00/6.18        | ~ (v1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup+', [status(thm)], ['22', '30'])).
% 6.00/6.18  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('33', plain,
% 6.00/6.18      ((r1_tarski @ sk_A @ 
% 6.00/6.18        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 6.00/6.18         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 6.00/6.18      inference('demod', [status(thm)], ['31', '32'])).
% 6.00/6.18  thf('34', plain,
% 6.00/6.18      (((r1_tarski @ sk_A @ 
% 6.00/6.18         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.00/6.18        | ~ (v1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup+', [status(thm)], ['2', '33'])).
% 6.00/6.18  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('36', plain,
% 6.00/6.18      ((r1_tarski @ sk_A @ 
% 6.00/6.18        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('demod', [status(thm)], ['34', '35'])).
% 6.00/6.18  thf('37', plain,
% 6.00/6.18      (![X2 : $i, X4 : $i]:
% 6.00/6.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 6.00/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.00/6.18  thf('38', plain,
% 6.00/6.18      ((~ (r1_tarski @ 
% 6.00/6.18           (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 6.00/6.18            (k9_relat_1 @ sk_B @ sk_A)) @ 
% 6.00/6.18           sk_A)
% 6.00/6.18        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 6.00/6.18            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 6.00/6.18      inference('sup-', [status(thm)], ['36', '37'])).
% 6.00/6.18  thf('39', plain,
% 6.00/6.18      (![X27 : $i, X28 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k7_relat_1 @ X27 @ X28)))),
% 6.00/6.18      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.00/6.18  thf('40', plain,
% 6.00/6.18      (![X31 : $i]:
% 6.00/6.18         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 6.00/6.18          | ~ (v1_relat_1 @ X31))),
% 6.00/6.18      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.00/6.18  thf('41', plain,
% 6.00/6.18      ((r1_tarski @ sk_A @ 
% 6.00/6.18        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 6.00/6.18         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 6.00/6.18      inference('demod', [status(thm)], ['31', '32'])).
% 6.00/6.18  thf('42', plain,
% 6.00/6.18      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 6.00/6.18        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['40', '41'])).
% 6.00/6.18  thf('43', plain,
% 6.00/6.18      ((~ (v1_relat_1 @ sk_B)
% 6.00/6.18        | (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 6.00/6.18      inference('sup-', [status(thm)], ['39', '42'])).
% 6.00/6.18  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('45', plain,
% 6.00/6.18      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('demod', [status(thm)], ['43', '44'])).
% 6.00/6.18  thf('46', plain,
% 6.00/6.18      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.00/6.18         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 6.00/6.18            = (k3_xboole_0 @ X34 @ (k10_relat_1 @ X35 @ X36)))
% 6.00/6.18          | ~ (v1_relat_1 @ X35))),
% 6.00/6.18      inference('cnf', [status(esa)], [t139_funct_1])).
% 6.00/6.18  thf('47', plain,
% 6.00/6.18      (![X31 : $i]:
% 6.00/6.18         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 6.00/6.18          | ~ (v1_relat_1 @ X31))),
% 6.00/6.18      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.00/6.18  thf('48', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (((k3_xboole_0 @ X0 @ 
% 6.00/6.18            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.00/6.18            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 6.00/6.18          | ~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['46', '47'])).
% 6.00/6.18  thf('49', plain,
% 6.00/6.18      (![X27 : $i, X28 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k7_relat_1 @ X27 @ X28)))),
% 6.00/6.18      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.00/6.18  thf('50', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | ((k3_xboole_0 @ X0 @ 
% 6.00/6.18              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 6.00/6.18              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 6.00/6.18      inference('clc', [status(thm)], ['48', '49'])).
% 6.00/6.18  thf('51', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 6.00/6.18      inference('simplify', [status(thm)], ['3'])).
% 6.00/6.18  thf(t18_xboole_1, axiom,
% 6.00/6.18    (![A:$i,B:$i,C:$i]:
% 6.00/6.18     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 6.00/6.18  thf('52', plain,
% 6.00/6.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.00/6.18         ((r1_tarski @ X10 @ X11)
% 6.00/6.18          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 6.00/6.18      inference('cnf', [status(esa)], [t18_xboole_1])).
% 6.00/6.18  thf('53', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 6.00/6.18      inference('sup-', [status(thm)], ['51', '52'])).
% 6.00/6.18  thf('54', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 6.00/6.18          | ~ (v1_relat_1 @ X1))),
% 6.00/6.18      inference('sup+', [status(thm)], ['50', '53'])).
% 6.00/6.18  thf('55', plain,
% 6.00/6.18      (![X2 : $i, X4 : $i]:
% 6.00/6.18         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 6.00/6.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.00/6.18  thf('56', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 6.00/6.18          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 6.00/6.18      inference('sup-', [status(thm)], ['54', '55'])).
% 6.00/6.18  thf('57', plain,
% 6.00/6.18      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 6.00/6.18        | ~ (v1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup-', [status(thm)], ['45', '56'])).
% 6.00/6.18  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('59', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('demod', [status(thm)], ['57', '58'])).
% 6.00/6.18  thf('60', plain,
% 6.00/6.18      (![X29 : $i, X30 : $i]:
% 6.00/6.18         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 6.00/6.18          | ~ (v1_relat_1 @ X29))),
% 6.00/6.18      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.00/6.18  thf('61', plain,
% 6.00/6.18      (![X31 : $i]:
% 6.00/6.18         (((k10_relat_1 @ X31 @ (k2_relat_1 @ X31)) = (k1_relat_1 @ X31))
% 6.00/6.18          | ~ (v1_relat_1 @ X31))),
% 6.00/6.18      inference('cnf', [status(esa)], [t169_relat_1])).
% 6.00/6.18  thf('62', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 6.00/6.18            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 6.00/6.18          | ~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['60', '61'])).
% 6.00/6.18  thf('63', plain,
% 6.00/6.18      (![X27 : $i, X28 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k7_relat_1 @ X27 @ X28)))),
% 6.00/6.18      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.00/6.18  thf('64', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 6.00/6.18              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 6.00/6.18      inference('clc', [status(thm)], ['62', '63'])).
% 6.00/6.18  thf('65', plain,
% 6.00/6.18      (![X29 : $i, X30 : $i]:
% 6.00/6.18         (((k2_relat_1 @ (k7_relat_1 @ X29 @ X30)) = (k9_relat_1 @ X29 @ X30))
% 6.00/6.18          | ~ (v1_relat_1 @ X29))),
% 6.00/6.18      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.00/6.18  thf('66', plain,
% 6.00/6.18      (![X32 : $i, X33 : $i]:
% 6.00/6.18         ((r1_tarski @ (k10_relat_1 @ X32 @ X33) @ 
% 6.00/6.18           (k10_relat_1 @ X32 @ (k2_relat_1 @ X32)))
% 6.00/6.18          | ~ (v1_relat_1 @ X32))),
% 6.00/6.18      inference('cnf', [status(esa)], [t170_relat_1])).
% 6.00/6.18  thf('67', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 6.00/6.18           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 6.00/6.18          | ~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['65', '66'])).
% 6.00/6.18  thf('68', plain,
% 6.00/6.18      (![X27 : $i, X28 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X27) | (v1_relat_1 @ (k7_relat_1 @ X27 @ X28)))),
% 6.00/6.18      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 6.00/6.18  thf('69', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 6.00/6.18             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 6.00/6.18      inference('clc', [status(thm)], ['67', '68'])).
% 6.00/6.18  thf('70', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 6.00/6.18           (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 6.00/6.18          | ~ (v1_relat_1 @ X1)
% 6.00/6.18          | ~ (v1_relat_1 @ X1))),
% 6.00/6.18      inference('sup+', [status(thm)], ['64', '69'])).
% 6.00/6.18  thf('71', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         (~ (v1_relat_1 @ X1)
% 6.00/6.18          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 6.00/6.18             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 6.00/6.18      inference('simplify', [status(thm)], ['70'])).
% 6.00/6.18  thf('72', plain,
% 6.00/6.18      (![X0 : $i]:
% 6.00/6.18         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 6.00/6.18          | ~ (v1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup+', [status(thm)], ['59', '71'])).
% 6.00/6.18  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('74', plain,
% 6.00/6.18      (![X0 : $i]:
% 6.00/6.18         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 6.00/6.18      inference('demod', [status(thm)], ['72', '73'])).
% 6.00/6.18  thf('75', plain,
% 6.00/6.18      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 6.00/6.18         = (sk_A))),
% 6.00/6.18      inference('demod', [status(thm)], ['38', '74'])).
% 6.00/6.18  thf('76', plain,
% 6.00/6.18      ((((k3_xboole_0 @ sk_A @ 
% 6.00/6.18          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 6.00/6.18        | ~ (v1_relat_1 @ sk_B))),
% 6.00/6.18      inference('sup+', [status(thm)], ['1', '75'])).
% 6.00/6.18  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 6.00/6.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.00/6.18  thf('78', plain,
% 6.00/6.18      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 6.00/6.18         = (sk_A))),
% 6.00/6.18      inference('demod', [status(thm)], ['76', '77'])).
% 6.00/6.18  thf('79', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 6.00/6.18      inference('simplify', [status(thm)], ['3'])).
% 6.00/6.18  thf(commutativity_k2_tarski, axiom,
% 6.00/6.18    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 6.00/6.18  thf('80', plain,
% 6.00/6.18      (![X23 : $i, X24 : $i]:
% 6.00/6.18         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 6.00/6.18      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 6.00/6.18  thf(t12_setfam_1, axiom,
% 6.00/6.18    (![A:$i,B:$i]:
% 6.00/6.18     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.00/6.18  thf('81', plain,
% 6.00/6.18      (![X25 : $i, X26 : $i]:
% 6.00/6.18         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 6.00/6.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.00/6.18  thf('82', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]:
% 6.00/6.18         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 6.00/6.18      inference('sup+', [status(thm)], ['80', '81'])).
% 6.00/6.18  thf('83', plain,
% 6.00/6.18      (![X25 : $i, X26 : $i]:
% 6.00/6.18         ((k1_setfam_1 @ (k2_tarski @ X25 @ X26)) = (k3_xboole_0 @ X25 @ X26))),
% 6.00/6.18      inference('cnf', [status(esa)], [t12_setfam_1])).
% 6.00/6.18  thf('84', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 6.00/6.18      inference('sup+', [status(thm)], ['82', '83'])).
% 6.00/6.18  thf('85', plain,
% 6.00/6.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.00/6.18         ((r1_tarski @ X10 @ X11)
% 6.00/6.18          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 6.00/6.18      inference('cnf', [status(esa)], [t18_xboole_1])).
% 6.00/6.18  thf('86', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.00/6.18         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 6.00/6.18      inference('sup-', [status(thm)], ['84', '85'])).
% 6.00/6.18  thf('87', plain,
% 6.00/6.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 6.00/6.18      inference('sup-', [status(thm)], ['79', '86'])).
% 6.00/6.18  thf('88', plain,
% 6.00/6.18      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 6.00/6.18      inference('sup+', [status(thm)], ['78', '87'])).
% 6.00/6.18  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 6.00/6.18  
% 6.00/6.18  % SZS output end Refutation
% 6.00/6.18  
% 6.00/6.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
