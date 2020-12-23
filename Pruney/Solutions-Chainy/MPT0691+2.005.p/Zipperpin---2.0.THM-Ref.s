%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYIdvuaAEg

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:18 EST 2020

% Result     : Theorem 3.33s
% Output     : Refutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 172 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  737 (1375 expanded)
%              Number of equality atoms :   45 (  68 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k3_xboole_0 @ X32 @ ( k10_relat_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X27 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X23: $i] :
      ( ( ( k9_relat_1 @ X23 @ ( k1_relat_1 @ X23 ) )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X26 @ X25 ) @ X24 )
        = ( k9_relat_1 @ X26 @ X24 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) @ X34 )
        = ( k3_xboole_0 @ X32 @ ( k10_relat_1 @ X33 @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('45',plain,(
    ! [X29: $i] :
      ( ( ( k10_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['57','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YYIdvuaAEg
% 0.15/0.37  % Computer   : n017.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:10:31 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 3.33/3.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.33/3.58  % Solved by: fo/fo7.sh
% 3.33/3.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.33/3.58  % done 7658 iterations in 3.095s
% 3.33/3.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.33/3.58  % SZS output start Refutation
% 3.33/3.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.33/3.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.33/3.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.33/3.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.33/3.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.33/3.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.33/3.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.33/3.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.33/3.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.33/3.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.33/3.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.33/3.58  thf(sk_A_type, type, sk_A: $i).
% 3.33/3.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.33/3.58  thf(sk_B_type, type, sk_B: $i).
% 3.33/3.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.33/3.58  thf(t146_funct_1, conjecture,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ B ) =>
% 3.33/3.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.33/3.58         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 3.33/3.58  thf(zf_stmt_0, negated_conjecture,
% 3.33/3.58    (~( ![A:$i,B:$i]:
% 3.33/3.58        ( ( v1_relat_1 @ B ) =>
% 3.33/3.58          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.33/3.58            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 3.33/3.58    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 3.33/3.58  thf('0', plain,
% 3.33/3.58      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf(t7_xboole_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.33/3.58  thf('1', plain,
% 3.33/3.58      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 3.33/3.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.33/3.58  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf(t1_xboole_1, axiom,
% 3.33/3.58    (![A:$i,B:$i,C:$i]:
% 3.33/3.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.33/3.58       ( r1_tarski @ A @ C ) ))).
% 3.33/3.58  thf('3', plain,
% 3.33/3.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.33/3.58         (~ (r1_tarski @ X5 @ X6)
% 3.33/3.58          | ~ (r1_tarski @ X6 @ X7)
% 3.33/3.58          | (r1_tarski @ X5 @ X7))),
% 3.33/3.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.33/3.58  thf('4', plain,
% 3.33/3.58      (![X0 : $i]:
% 3.33/3.58         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 3.33/3.58      inference('sup-', [status(thm)], ['2', '3'])).
% 3.33/3.58  thf('5', plain,
% 3.33/3.58      (![X0 : $i]:
% 3.33/3.58         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 3.33/3.58      inference('sup-', [status(thm)], ['1', '4'])).
% 3.33/3.58  thf(t43_xboole_1, axiom,
% 3.33/3.58    (![A:$i,B:$i,C:$i]:
% 3.33/3.58     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.33/3.58       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.33/3.58  thf('6', plain,
% 3.33/3.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.58         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.33/3.58          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.33/3.58      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.33/3.58  thf('7', plain,
% 3.33/3.58      (![X0 : $i]:
% 3.33/3.58         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) @ X0)),
% 3.33/3.58      inference('sup-', [status(thm)], ['5', '6'])).
% 3.33/3.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.33/3.58  thf('8', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 3.33/3.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.33/3.58  thf(d10_xboole_0, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.33/3.58  thf('9', plain,
% 3.33/3.58      (![X2 : $i, X4 : $i]:
% 3.33/3.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.33/3.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.33/3.58  thf('10', plain,
% 3.33/3.58      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.33/3.58      inference('sup-', [status(thm)], ['8', '9'])).
% 3.33/3.58  thf('11', plain,
% 3.33/3.58      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 3.33/3.58      inference('sup-', [status(thm)], ['7', '10'])).
% 3.33/3.58  thf(t48_xboole_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.33/3.58  thf('12', plain,
% 3.33/3.58      (![X13 : $i, X14 : $i]:
% 3.33/3.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.33/3.58           = (k3_xboole_0 @ X13 @ X14))),
% 3.33/3.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.33/3.58  thf('13', plain,
% 3.33/3.58      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 3.33/3.58         = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.33/3.58      inference('sup+', [status(thm)], ['11', '12'])).
% 3.33/3.58  thf(t3_boole, axiom,
% 3.33/3.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.33/3.58  thf('14', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.33/3.58      inference('cnf', [status(esa)], [t3_boole])).
% 3.33/3.58  thf('15', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 3.33/3.58      inference('demod', [status(thm)], ['13', '14'])).
% 3.33/3.58  thf(t169_relat_1, axiom,
% 3.33/3.58    (![A:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ A ) =>
% 3.33/3.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 3.33/3.58  thf('16', plain,
% 3.33/3.58      (![X29 : $i]:
% 3.33/3.58         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 3.33/3.58          | ~ (v1_relat_1 @ X29))),
% 3.33/3.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 3.33/3.58  thf(t139_funct_1, axiom,
% 3.33/3.58    (![A:$i,B:$i,C:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ C ) =>
% 3.33/3.58       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.33/3.58         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.33/3.58  thf('17', plain,
% 3.33/3.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.33/3.58         (((k10_relat_1 @ (k7_relat_1 @ X33 @ X32) @ X34)
% 3.33/3.58            = (k3_xboole_0 @ X32 @ (k10_relat_1 @ X33 @ X34)))
% 3.33/3.58          | ~ (v1_relat_1 @ X33))),
% 3.33/3.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.33/3.58  thf(t167_relat_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ B ) =>
% 3.33/3.58       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 3.33/3.58  thf('18', plain,
% 3.33/3.58      (![X27 : $i, X28 : $i]:
% 3.33/3.58         ((r1_tarski @ (k10_relat_1 @ X27 @ X28) @ (k1_relat_1 @ X27))
% 3.33/3.58          | ~ (v1_relat_1 @ X27))),
% 3.33/3.58      inference('cnf', [status(esa)], [t167_relat_1])).
% 3.33/3.58  thf('19', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.58         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 3.33/3.58           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 3.33/3.58          | ~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 3.33/3.58      inference('sup+', [status(thm)], ['17', '18'])).
% 3.33/3.58  thf(dt_k7_relat_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.33/3.58  thf('20', plain,
% 3.33/3.58      (![X21 : $i, X22 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 3.33/3.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.33/3.58  thf('21', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X1)
% 3.33/3.58          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 3.33/3.58             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 3.33/3.58      inference('clc', [status(thm)], ['19', '20'])).
% 3.33/3.58  thf('22', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         ((r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.33/3.58           (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)))
% 3.33/3.58          | ~ (v1_relat_1 @ X0)
% 3.33/3.58          | ~ (v1_relat_1 @ X0))),
% 3.33/3.58      inference('sup+', [status(thm)], ['16', '21'])).
% 3.33/3.58  thf('23', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X0)
% 3.33/3.58          | (r1_tarski @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 3.33/3.58             (k1_relat_1 @ (k7_relat_1 @ X0 @ X1))))),
% 3.33/3.58      inference('simplify', [status(thm)], ['22'])).
% 3.33/3.58  thf('24', plain,
% 3.33/3.58      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.33/3.58        | ~ (v1_relat_1 @ sk_B))),
% 3.33/3.58      inference('sup+', [status(thm)], ['15', '23'])).
% 3.33/3.58  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf('26', plain,
% 3.33/3.58      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 3.33/3.58      inference('demod', [status(thm)], ['24', '25'])).
% 3.33/3.58  thf(t87_relat_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ B ) =>
% 3.33/3.58       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 3.33/3.58  thf('27', plain,
% 3.33/3.58      (![X30 : $i, X31 : $i]:
% 3.33/3.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ X31)
% 3.33/3.58          | ~ (v1_relat_1 @ X30))),
% 3.33/3.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 3.33/3.58  thf('28', plain,
% 3.33/3.58      (![X2 : $i, X4 : $i]:
% 3.33/3.58         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.33/3.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.33/3.58  thf('29', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.33/3.58          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 3.33/3.58      inference('sup-', [status(thm)], ['27', '28'])).
% 3.33/3.58  thf('30', plain,
% 3.33/3.58      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.33/3.58        | ~ (v1_relat_1 @ sk_B))),
% 3.33/3.58      inference('sup-', [status(thm)], ['26', '29'])).
% 3.33/3.58  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf('32', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 3.33/3.58      inference('demod', [status(thm)], ['30', '31'])).
% 3.33/3.58  thf(t146_relat_1, axiom,
% 3.33/3.58    (![A:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ A ) =>
% 3.33/3.58       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 3.33/3.58  thf('33', plain,
% 3.33/3.58      (![X23 : $i]:
% 3.33/3.58         (((k9_relat_1 @ X23 @ (k1_relat_1 @ X23)) = (k2_relat_1 @ X23))
% 3.33/3.58          | ~ (v1_relat_1 @ X23))),
% 3.33/3.58      inference('cnf', [status(esa)], [t146_relat_1])).
% 3.33/3.58  thf('34', plain,
% 3.33/3.58      (![X30 : $i, X31 : $i]:
% 3.33/3.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ X31)
% 3.33/3.58          | ~ (v1_relat_1 @ X30))),
% 3.33/3.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 3.33/3.58  thf(t162_relat_1, axiom,
% 3.33/3.58    (![A:$i]:
% 3.33/3.58     ( ( v1_relat_1 @ A ) =>
% 3.33/3.58       ( ![B:$i,C:$i]:
% 3.33/3.58         ( ( r1_tarski @ B @ C ) =>
% 3.33/3.58           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 3.33/3.58             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 3.33/3.58  thf('35', plain,
% 3.33/3.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.33/3.58         (~ (r1_tarski @ X24 @ X25)
% 3.33/3.58          | ((k9_relat_1 @ (k7_relat_1 @ X26 @ X25) @ X24)
% 3.33/3.58              = (k9_relat_1 @ X26 @ X24))
% 3.33/3.58          | ~ (v1_relat_1 @ X26))),
% 3.33/3.58      inference('cnf', [status(esa)], [t162_relat_1])).
% 3.33/3.58  thf('36', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (v1_relat_1 @ X2)
% 3.33/3.58          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 3.33/3.58              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.33/3.58              = (k9_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.33/3.58      inference('sup-', [status(thm)], ['34', '35'])).
% 3.33/3.58  thf('37', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.33/3.58            = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.33/3.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.33/3.58          | ~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (v1_relat_1 @ X1))),
% 3.33/3.58      inference('sup+', [status(thm)], ['33', '36'])).
% 3.33/3.58  thf('38', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.33/3.58          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.33/3.58              = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 3.33/3.58      inference('simplify', [status(thm)], ['37'])).
% 3.33/3.58  thf('39', plain,
% 3.33/3.58      (![X21 : $i, X22 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 3.33/3.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.33/3.58  thf('40', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.33/3.58            = (k9_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.33/3.58          | ~ (v1_relat_1 @ X1))),
% 3.33/3.58      inference('clc', [status(thm)], ['38', '39'])).
% 3.33/3.58  thf('41', plain,
% 3.33/3.58      ((((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))
% 3.33/3.58        | ~ (v1_relat_1 @ sk_B))),
% 3.33/3.58      inference('sup+', [status(thm)], ['32', '40'])).
% 3.33/3.58  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf('43', plain,
% 3.33/3.58      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k9_relat_1 @ sk_B @ sk_A))),
% 3.33/3.58      inference('demod', [status(thm)], ['41', '42'])).
% 3.33/3.58  thf('44', plain,
% 3.33/3.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.33/3.58         (((k10_relat_1 @ (k7_relat_1 @ X33 @ X32) @ X34)
% 3.33/3.58            = (k3_xboole_0 @ X32 @ (k10_relat_1 @ X33 @ X34)))
% 3.33/3.58          | ~ (v1_relat_1 @ X33))),
% 3.33/3.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.33/3.58  thf('45', plain,
% 3.33/3.58      (![X29 : $i]:
% 3.33/3.58         (((k10_relat_1 @ X29 @ (k2_relat_1 @ X29)) = (k1_relat_1 @ X29))
% 3.33/3.58          | ~ (v1_relat_1 @ X29))),
% 3.33/3.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 3.33/3.58  thf('46', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (((k3_xboole_0 @ X0 @ 
% 3.33/3.58            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.33/3.58            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 3.33/3.58          | ~ (v1_relat_1 @ X1)
% 3.33/3.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.33/3.58      inference('sup+', [status(thm)], ['44', '45'])).
% 3.33/3.58  thf('47', plain,
% 3.33/3.58      (![X21 : $i, X22 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X21) | (v1_relat_1 @ (k7_relat_1 @ X21 @ X22)))),
% 3.33/3.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.33/3.58  thf('48', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         (~ (v1_relat_1 @ X1)
% 3.33/3.58          | ((k3_xboole_0 @ X0 @ 
% 3.33/3.58              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 3.33/3.58              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 3.33/3.58      inference('clc', [status(thm)], ['46', '47'])).
% 3.33/3.58  thf('49', plain,
% 3.33/3.58      ((((k3_xboole_0 @ sk_A @ 
% 3.33/3.58          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 3.33/3.58          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 3.33/3.58        | ~ (v1_relat_1 @ sk_B))),
% 3.33/3.58      inference('sup+', [status(thm)], ['43', '48'])).
% 3.33/3.58  thf('50', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 3.33/3.58      inference('demod', [status(thm)], ['30', '31'])).
% 3.33/3.58  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 3.33/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.33/3.58  thf('52', plain,
% 3.33/3.58      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 3.33/3.58         = (sk_A))),
% 3.33/3.58      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.33/3.58  thf(commutativity_k2_tarski, axiom,
% 3.33/3.58    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.33/3.58  thf('53', plain,
% 3.33/3.58      (![X17 : $i, X18 : $i]:
% 3.33/3.58         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 3.33/3.58      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.33/3.58  thf(t12_setfam_1, axiom,
% 3.33/3.58    (![A:$i,B:$i]:
% 3.33/3.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.33/3.58  thf('54', plain,
% 3.33/3.58      (![X19 : $i, X20 : $i]:
% 3.33/3.58         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 3.33/3.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.33/3.58  thf('55', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]:
% 3.33/3.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.33/3.58      inference('sup+', [status(thm)], ['53', '54'])).
% 3.33/3.58  thf('56', plain,
% 3.33/3.58      (![X19 : $i, X20 : $i]:
% 3.33/3.58         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 3.33/3.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.33/3.58  thf('57', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.33/3.58      inference('sup+', [status(thm)], ['55', '56'])).
% 3.33/3.58  thf('58', plain,
% 3.33/3.58      (![X13 : $i, X14 : $i]:
% 3.33/3.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.33/3.58           = (k3_xboole_0 @ X13 @ X14))),
% 3.33/3.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.33/3.58  thf(commutativity_k2_xboole_0, axiom,
% 3.33/3.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.33/3.58  thf('59', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.33/3.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.33/3.58  thf('60', plain,
% 3.33/3.58      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 3.33/3.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.33/3.58  thf('61', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.33/3.58      inference('sup+', [status(thm)], ['59', '60'])).
% 3.33/3.58  thf('62', plain,
% 3.33/3.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.33/3.58         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.33/3.58          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.33/3.58      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.33/3.58  thf('63', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 3.33/3.58      inference('sup-', [status(thm)], ['61', '62'])).
% 3.33/3.58  thf('64', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 3.33/3.58      inference('sup+', [status(thm)], ['58', '63'])).
% 3.33/3.58  thf('65', plain,
% 3.33/3.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.33/3.58      inference('sup+', [status(thm)], ['57', '64'])).
% 3.33/3.58  thf('66', plain,
% 3.33/3.58      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 3.33/3.58      inference('sup+', [status(thm)], ['52', '65'])).
% 3.33/3.58  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 3.33/3.58  
% 3.33/3.58  % SZS output end Refutation
% 3.33/3.58  
% 3.42/3.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
