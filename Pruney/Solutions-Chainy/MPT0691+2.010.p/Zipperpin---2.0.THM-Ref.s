%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DMn5qTyysC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:18 EST 2020

% Result     : Theorem 8.35s
% Output     : Refutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 347 expanded)
%              Number of leaves         :   35 ( 118 expanded)
%              Depth                    :   26
%              Number of atoms          : 1031 (2844 expanded)
%              Number of equality atoms :   67 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k3_xboole_0 @ X37 @ ( k10_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k3_xboole_0 @ X37 @ ( k10_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X33 @ X34 ) @ ( k10_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k3_xboole_0 @ X37 @ ( k10_relat_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('42',plain,(
    ! [X32: $i] :
      ( ( ( k10_relat_1 @ X32 @ ( k2_relat_1 @ X32 ) )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X33 @ X34 ) @ ( k10_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('52',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) ) @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69','71','72'])).

thf('74',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['76','89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('92',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_tarski @ X29 @ X30 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X31 @ X30 ) @ X29 )
        = ( k9_relat_1 @ X31 @ X29 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('95',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X28: $i] :
      ( ( ( k9_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('97',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['93','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DMn5qTyysC
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.35/8.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.35/8.54  % Solved by: fo/fo7.sh
% 8.35/8.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.35/8.54  % done 11139 iterations in 8.078s
% 8.35/8.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.35/8.54  % SZS output start Refutation
% 8.35/8.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.35/8.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.35/8.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.35/8.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.35/8.54  thf(sk_B_type, type, sk_B: $i).
% 8.35/8.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.35/8.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.35/8.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 8.35/8.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.35/8.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.35/8.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.35/8.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.35/8.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.35/8.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 8.35/8.54  thf(sk_A_type, type, sk_A: $i).
% 8.35/8.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.35/8.54  thf(t146_funct_1, conjecture,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ B ) =>
% 8.35/8.54       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 8.35/8.54         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 8.35/8.54  thf(zf_stmt_0, negated_conjecture,
% 8.35/8.54    (~( ![A:$i,B:$i]:
% 8.35/8.54        ( ( v1_relat_1 @ B ) =>
% 8.35/8.54          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 8.35/8.54            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 8.35/8.54    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 8.35/8.54  thf('0', plain,
% 8.35/8.54      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf(t139_funct_1, axiom,
% 8.35/8.54    (![A:$i,B:$i,C:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ C ) =>
% 8.35/8.54       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 8.35/8.54         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 8.35/8.54  thf('1', plain,
% 8.35/8.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.35/8.54         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 8.35/8.54            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 8.35/8.54          | ~ (v1_relat_1 @ X38))),
% 8.35/8.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 8.35/8.54  thf('2', plain,
% 8.35/8.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.35/8.54         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 8.35/8.54            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 8.35/8.54          | ~ (v1_relat_1 @ X38))),
% 8.35/8.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 8.35/8.54  thf(t169_relat_1, axiom,
% 8.35/8.54    (![A:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ A ) =>
% 8.35/8.54       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 8.35/8.54  thf('3', plain,
% 8.35/8.54      (![X32 : $i]:
% 8.35/8.54         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 8.35/8.54          | ~ (v1_relat_1 @ X32))),
% 8.35/8.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.35/8.54  thf('4', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (((k3_xboole_0 @ X0 @ 
% 8.35/8.54            (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 8.35/8.54            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 8.35/8.54          | ~ (v1_relat_1 @ X1)
% 8.35/8.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 8.35/8.54      inference('sup+', [status(thm)], ['2', '3'])).
% 8.35/8.54  thf(dt_k7_relat_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 8.35/8.54  thf('5', plain,
% 8.35/8.54      (![X26 : $i, X27 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 8.35/8.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 8.35/8.54  thf('6', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X1)
% 8.35/8.54          | ((k3_xboole_0 @ X0 @ 
% 8.35/8.54              (k10_relat_1 @ X1 @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 8.35/8.54              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 8.35/8.54      inference('clc', [status(thm)], ['4', '5'])).
% 8.35/8.54  thf('7', plain,
% 8.35/8.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.35/8.54         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 8.35/8.54            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 8.35/8.54          | ~ (v1_relat_1 @ X38))),
% 8.35/8.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 8.35/8.54  thf('8', plain,
% 8.35/8.54      (![X26 : $i, X27 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 8.35/8.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 8.35/8.54  thf('9', plain,
% 8.35/8.54      (![X32 : $i]:
% 8.35/8.54         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 8.35/8.54          | ~ (v1_relat_1 @ X32))),
% 8.35/8.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.35/8.54  thf(t170_relat_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ B ) =>
% 8.35/8.54       ( r1_tarski @
% 8.35/8.54         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 8.35/8.54  thf('10', plain,
% 8.35/8.54      (![X33 : $i, X34 : $i]:
% 8.35/8.54         ((r1_tarski @ (k10_relat_1 @ X33 @ X34) @ 
% 8.35/8.54           (k10_relat_1 @ X33 @ (k2_relat_1 @ X33)))
% 8.35/8.54          | ~ (v1_relat_1 @ X33))),
% 8.35/8.54      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.35/8.54  thf('11', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 8.35/8.54           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 8.35/8.54          | ~ (v1_relat_1 @ X0)
% 8.35/8.54          | ~ (v1_relat_1 @ X0))),
% 8.35/8.54      inference('sup+', [status(thm)], ['9', '10'])).
% 8.35/8.54  thf('12', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X0)
% 8.35/8.54          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 8.35/8.54             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 8.35/8.54      inference('simplify', [status(thm)], ['11'])).
% 8.35/8.54  thf('13', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf(t1_xboole_1, axiom,
% 8.35/8.54    (![A:$i,B:$i,C:$i]:
% 8.35/8.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.35/8.54       ( r1_tarski @ A @ C ) ))).
% 8.35/8.54  thf('14', plain,
% 8.35/8.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 8.35/8.54         (~ (r1_tarski @ X3 @ X4)
% 8.35/8.54          | ~ (r1_tarski @ X4 @ X5)
% 8.35/8.54          | (r1_tarski @ X3 @ X5))),
% 8.35/8.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.35/8.54  thf('15', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 8.35/8.54      inference('sup-', [status(thm)], ['13', '14'])).
% 8.35/8.54  thf('16', plain,
% 8.35/8.54      ((~ (v1_relat_1 @ sk_B)
% 8.35/8.54        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 8.35/8.54      inference('sup-', [status(thm)], ['12', '15'])).
% 8.35/8.54  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('18', plain,
% 8.35/8.54      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 8.35/8.54      inference('demod', [status(thm)], ['16', '17'])).
% 8.35/8.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.35/8.54  thf('19', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 8.35/8.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.35/8.54  thf(t45_xboole_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( r1_tarski @ A @ B ) =>
% 8.35/8.54       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 8.35/8.54  thf('20', plain,
% 8.35/8.54      (![X14 : $i, X15 : $i]:
% 8.35/8.54         (((X15) = (k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))
% 8.35/8.54          | ~ (r1_tarski @ X14 @ X15))),
% 8.35/8.54      inference('cnf', [status(esa)], [t45_xboole_1])).
% 8.35/8.54  thf('21', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 8.35/8.54      inference('sup-', [status(thm)], ['19', '20'])).
% 8.35/8.54  thf(t3_boole, axiom,
% 8.35/8.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.35/8.54  thf('22', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 8.35/8.54      inference('cnf', [status(esa)], [t3_boole])).
% 8.35/8.54  thf('23', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 8.35/8.54      inference('demod', [status(thm)], ['21', '22'])).
% 8.35/8.54  thf(commutativity_k2_tarski, axiom,
% 8.35/8.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 8.35/8.54  thf('24', plain,
% 8.35/8.54      (![X20 : $i, X21 : $i]:
% 8.35/8.54         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 8.35/8.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.35/8.54  thf(l51_zfmisc_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.35/8.54  thf('25', plain,
% 8.35/8.54      (![X22 : $i, X23 : $i]:
% 8.35/8.54         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 8.35/8.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.35/8.54  thf('26', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 8.35/8.54      inference('sup+', [status(thm)], ['24', '25'])).
% 8.35/8.54  thf('27', plain,
% 8.35/8.54      (![X22 : $i, X23 : $i]:
% 8.35/8.54         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 8.35/8.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.35/8.54  thf('28', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.35/8.54      inference('sup+', [status(thm)], ['26', '27'])).
% 8.35/8.54  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.35/8.54      inference('sup+', [status(thm)], ['23', '28'])).
% 8.35/8.54  thf(t43_xboole_1, axiom,
% 8.35/8.54    (![A:$i,B:$i,C:$i]:
% 8.35/8.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 8.35/8.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 8.35/8.54  thf('30', plain,
% 8.35/8.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.35/8.54         ((r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 8.35/8.54          | ~ (r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 8.35/8.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.35/8.54  thf('31', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (r1_tarski @ X1 @ X0)
% 8.35/8.54          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 8.35/8.54      inference('sup-', [status(thm)], ['29', '30'])).
% 8.35/8.54  thf('32', plain,
% 8.35/8.54      ((r1_tarski @ 
% 8.35/8.54        (k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))) @ 
% 8.35/8.54        k1_xboole_0)),
% 8.35/8.54      inference('sup-', [status(thm)], ['18', '31'])).
% 8.35/8.54  thf('33', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 8.35/8.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.35/8.54  thf(d10_xboole_0, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.35/8.54  thf('34', plain,
% 8.35/8.54      (![X0 : $i, X2 : $i]:
% 8.35/8.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.35/8.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.54  thf('35', plain,
% 8.35/8.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.35/8.54      inference('sup-', [status(thm)], ['33', '34'])).
% 8.35/8.54  thf('36', plain,
% 8.35/8.54      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 8.35/8.54         = (k1_xboole_0))),
% 8.35/8.54      inference('sup-', [status(thm)], ['32', '35'])).
% 8.35/8.54  thf(t48_xboole_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.35/8.54  thf('37', plain,
% 8.35/8.54      (![X16 : $i, X17 : $i]:
% 8.35/8.54         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 8.35/8.54           = (k3_xboole_0 @ X16 @ X17))),
% 8.35/8.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.35/8.54  thf('38', plain,
% 8.35/8.54      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 8.35/8.54         = (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 8.35/8.54      inference('sup+', [status(thm)], ['36', '37'])).
% 8.35/8.54  thf('39', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 8.35/8.54      inference('cnf', [status(esa)], [t3_boole])).
% 8.35/8.54  thf('40', plain,
% 8.35/8.54      (((sk_A)
% 8.35/8.54         = (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 8.35/8.54      inference('demod', [status(thm)], ['38', '39'])).
% 8.35/8.54  thf('41', plain,
% 8.35/8.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.35/8.54         (((k10_relat_1 @ (k7_relat_1 @ X38 @ X37) @ X39)
% 8.35/8.54            = (k3_xboole_0 @ X37 @ (k10_relat_1 @ X38 @ X39)))
% 8.35/8.54          | ~ (v1_relat_1 @ X38))),
% 8.35/8.54      inference('cnf', [status(esa)], [t139_funct_1])).
% 8.35/8.54  thf('42', plain,
% 8.35/8.54      (![X32 : $i]:
% 8.35/8.54         (((k10_relat_1 @ X32 @ (k2_relat_1 @ X32)) = (k1_relat_1 @ X32))
% 8.35/8.54          | ~ (v1_relat_1 @ X32))),
% 8.35/8.54      inference('cnf', [status(esa)], [t169_relat_1])).
% 8.35/8.54  thf('43', plain,
% 8.35/8.54      (![X33 : $i, X34 : $i]:
% 8.35/8.54         ((r1_tarski @ (k10_relat_1 @ X33 @ X34) @ 
% 8.35/8.54           (k10_relat_1 @ X33 @ (k2_relat_1 @ X33)))
% 8.35/8.54          | ~ (v1_relat_1 @ X33))),
% 8.35/8.54      inference('cnf', [status(esa)], [t170_relat_1])).
% 8.35/8.54  thf('44', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 8.35/8.54          | ~ (v1_relat_1 @ X0)
% 8.35/8.54          | ~ (v1_relat_1 @ X0))),
% 8.35/8.54      inference('sup+', [status(thm)], ['42', '43'])).
% 8.35/8.54  thf('45', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X0)
% 8.35/8.54          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 8.35/8.54      inference('simplify', [status(thm)], ['44'])).
% 8.35/8.54  thf('46', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.54         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 8.35/8.54           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 8.35/8.54          | ~ (v1_relat_1 @ X1)
% 8.35/8.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 8.35/8.54      inference('sup+', [status(thm)], ['41', '45'])).
% 8.35/8.54  thf('47', plain,
% 8.35/8.54      (![X26 : $i, X27 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 8.35/8.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 8.35/8.54  thf('48', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X1)
% 8.35/8.54          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 8.35/8.54             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 8.35/8.54      inference('clc', [status(thm)], ['46', '47'])).
% 8.35/8.54  thf('49', plain,
% 8.35/8.54      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 8.35/8.54        | ~ (v1_relat_1 @ sk_B))),
% 8.35/8.54      inference('sup+', [status(thm)], ['40', '48'])).
% 8.35/8.54  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('51', plain,
% 8.35/8.54      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['49', '50'])).
% 8.35/8.54  thf(t87_relat_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ B ) =>
% 8.35/8.54       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 8.35/8.54  thf('52', plain,
% 8.35/8.54      (![X35 : $i, X36 : $i]:
% 8.35/8.54         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X35 @ X36)) @ X36)
% 8.35/8.54          | ~ (v1_relat_1 @ X35))),
% 8.35/8.54      inference('cnf', [status(esa)], [t87_relat_1])).
% 8.35/8.54  thf('53', plain,
% 8.35/8.54      (![X0 : $i, X2 : $i]:
% 8.35/8.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.35/8.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.54  thf('54', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X1)
% 8.35/8.54          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 8.35/8.54          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 8.35/8.54      inference('sup-', [status(thm)], ['52', '53'])).
% 8.35/8.54  thf('55', plain,
% 8.35/8.54      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 8.35/8.54        | ~ (v1_relat_1 @ sk_B))),
% 8.35/8.54      inference('sup-', [status(thm)], ['51', '54'])).
% 8.35/8.54  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('57', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['55', '56'])).
% 8.35/8.54  thf('58', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X0)
% 8.35/8.54          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 8.35/8.54      inference('simplify', [status(thm)], ['44'])).
% 8.35/8.54  thf('59', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 8.35/8.54          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('sup+', [status(thm)], ['57', '58'])).
% 8.35/8.54  thf('60', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ sk_B)
% 8.35/8.54          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 8.35/8.54      inference('sup-', [status(thm)], ['8', '59'])).
% 8.35/8.54  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('62', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 8.35/8.54      inference('demod', [status(thm)], ['60', '61'])).
% 8.35/8.54  thf('63', plain,
% 8.35/8.54      (![X0 : $i, X2 : $i]:
% 8.35/8.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.35/8.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.54  thf('64', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 8.35/8.54          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 8.35/8.54      inference('sup-', [status(thm)], ['62', '63'])).
% 8.35/8.54  thf('65', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (~ (r1_tarski @ sk_A @ 
% 8.35/8.54             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 8.35/8.54          | ~ (v1_relat_1 @ sk_B)
% 8.35/8.54          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 8.35/8.54      inference('sup-', [status(thm)], ['7', '64'])).
% 8.35/8.54  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('67', plain,
% 8.35/8.54      (![X0 : $i]:
% 8.35/8.54         (~ (r1_tarski @ sk_A @ 
% 8.35/8.54             (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 8.35/8.54          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 8.35/8.54      inference('demod', [status(thm)], ['65', '66'])).
% 8.35/8.54  thf('68', plain,
% 8.35/8.54      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 8.35/8.54        | ~ (v1_relat_1 @ sk_B)
% 8.35/8.54        | ((sk_A)
% 8.35/8.54            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 8.35/8.54               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 8.35/8.54      inference('sup-', [status(thm)], ['6', '67'])).
% 8.35/8.54  thf('69', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['55', '56'])).
% 8.35/8.54  thf('70', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.35/8.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.35/8.54  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.35/8.54      inference('simplify', [status(thm)], ['70'])).
% 8.35/8.54  thf('72', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('73', plain,
% 8.35/8.54      (((sk_A)
% 8.35/8.54         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 8.35/8.54            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 8.35/8.54      inference('demod', [status(thm)], ['68', '69', '71', '72'])).
% 8.35/8.54  thf('74', plain,
% 8.35/8.54      ((((sk_A)
% 8.35/8.54          = (k3_xboole_0 @ sk_A @ 
% 8.35/8.54             (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))
% 8.35/8.54        | ~ (v1_relat_1 @ sk_B))),
% 8.35/8.54      inference('sup+', [status(thm)], ['1', '73'])).
% 8.35/8.54  thf('75', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('76', plain,
% 8.35/8.54      (((sk_A)
% 8.35/8.54         = (k3_xboole_0 @ sk_A @ 
% 8.35/8.54            (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 8.35/8.54      inference('demod', [status(thm)], ['74', '75'])).
% 8.35/8.54  thf('77', plain,
% 8.35/8.54      (![X20 : $i, X21 : $i]:
% 8.35/8.54         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 8.35/8.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.35/8.54  thf(t12_setfam_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]:
% 8.35/8.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.35/8.54  thf('78', plain,
% 8.35/8.54      (![X24 : $i, X25 : $i]:
% 8.35/8.54         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 8.35/8.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.35/8.54  thf('79', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.54      inference('sup+', [status(thm)], ['77', '78'])).
% 8.35/8.54  thf('80', plain,
% 8.35/8.54      (![X24 : $i, X25 : $i]:
% 8.35/8.54         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 8.35/8.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.35/8.54  thf('81', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.35/8.54      inference('sup+', [status(thm)], ['79', '80'])).
% 8.35/8.54  thf('82', plain,
% 8.35/8.54      (![X16 : $i, X17 : $i]:
% 8.35/8.54         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 8.35/8.54           = (k3_xboole_0 @ X16 @ X17))),
% 8.35/8.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.35/8.54  thf('83', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 8.35/8.54      inference('sup+', [status(thm)], ['26', '27'])).
% 8.35/8.54  thf(t7_xboole_1, axiom,
% 8.35/8.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.35/8.54  thf('84', plain,
% 8.35/8.54      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 8.35/8.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.35/8.54  thf('85', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 8.35/8.54      inference('sup+', [status(thm)], ['83', '84'])).
% 8.35/8.54  thf('86', plain,
% 8.35/8.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 8.35/8.54         ((r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 8.35/8.54          | ~ (r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 8.35/8.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.35/8.54  thf('87', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 8.35/8.54      inference('sup-', [status(thm)], ['85', '86'])).
% 8.35/8.54  thf('88', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 8.35/8.54      inference('sup+', [status(thm)], ['82', '87'])).
% 8.35/8.54  thf('89', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 8.35/8.54      inference('sup+', [status(thm)], ['81', '88'])).
% 8.35/8.54  thf('90', plain,
% 8.35/8.54      ((r1_tarski @ sk_A @ 
% 8.35/8.54        (k10_relat_1 @ sk_B @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 8.35/8.54      inference('sup+', [status(thm)], ['76', '89'])).
% 8.35/8.54  thf('91', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.35/8.54      inference('simplify', [status(thm)], ['70'])).
% 8.35/8.54  thf(t162_relat_1, axiom,
% 8.35/8.54    (![A:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ A ) =>
% 8.35/8.54       ( ![B:$i,C:$i]:
% 8.35/8.54         ( ( r1_tarski @ B @ C ) =>
% 8.35/8.54           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 8.35/8.54             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 8.35/8.54  thf('92', plain,
% 8.35/8.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 8.35/8.54         (~ (r1_tarski @ X29 @ X30)
% 8.35/8.54          | ((k9_relat_1 @ (k7_relat_1 @ X31 @ X30) @ X29)
% 8.35/8.54              = (k9_relat_1 @ X31 @ X29))
% 8.35/8.54          | ~ (v1_relat_1 @ X31))),
% 8.35/8.54      inference('cnf', [status(esa)], [t162_relat_1])).
% 8.35/8.54  thf('93', plain,
% 8.35/8.54      (![X0 : $i, X1 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X1)
% 8.35/8.54          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 8.35/8.54              = (k9_relat_1 @ X1 @ X0)))),
% 8.35/8.54      inference('sup-', [status(thm)], ['91', '92'])).
% 8.35/8.54  thf('94', plain,
% 8.35/8.54      (![X26 : $i, X27 : $i]:
% 8.35/8.54         (~ (v1_relat_1 @ X26) | (v1_relat_1 @ (k7_relat_1 @ X26 @ X27)))),
% 8.35/8.54      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 8.35/8.54  thf('95', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['55', '56'])).
% 8.35/8.54  thf(t146_relat_1, axiom,
% 8.35/8.54    (![A:$i]:
% 8.35/8.54     ( ( v1_relat_1 @ A ) =>
% 8.35/8.54       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 8.35/8.54  thf('96', plain,
% 8.35/8.54      (![X28 : $i]:
% 8.35/8.54         (((k9_relat_1 @ X28 @ (k1_relat_1 @ X28)) = (k2_relat_1 @ X28))
% 8.35/8.54          | ~ (v1_relat_1 @ X28))),
% 8.35/8.54      inference('cnf', [status(esa)], [t146_relat_1])).
% 8.35/8.54  thf('97', plain,
% 8.35/8.54      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 8.35/8.54          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 8.35/8.54        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('sup+', [status(thm)], ['95', '96'])).
% 8.35/8.54  thf('98', plain,
% 8.35/8.54      ((~ (v1_relat_1 @ sk_B)
% 8.35/8.54        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 8.35/8.54            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 8.35/8.54      inference('sup-', [status(thm)], ['94', '97'])).
% 8.35/8.54  thf('99', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('100', plain,
% 8.35/8.54      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 8.35/8.54         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['98', '99'])).
% 8.35/8.54  thf('101', plain,
% 8.35/8.54      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 8.35/8.54        | ~ (v1_relat_1 @ sk_B))),
% 8.35/8.54      inference('sup+', [status(thm)], ['93', '100'])).
% 8.35/8.54  thf('102', plain, ((v1_relat_1 @ sk_B)),
% 8.35/8.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.35/8.54  thf('103', plain,
% 8.35/8.54      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['101', '102'])).
% 8.35/8.54  thf('104', plain,
% 8.35/8.54      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 8.35/8.54      inference('demod', [status(thm)], ['90', '103'])).
% 8.35/8.54  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 8.35/8.54  
% 8.35/8.54  % SZS output end Refutation
% 8.35/8.54  
% 8.35/8.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
