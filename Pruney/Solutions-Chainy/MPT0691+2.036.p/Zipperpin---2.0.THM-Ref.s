%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y40fXI8C3W

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:22 EST 2020

% Result     : Theorem 5.04s
% Output     : Refutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 199 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  754 (1685 expanded)
%              Number of equality atoms :   43 (  76 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k9_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X30: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X30: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','27'])).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k3_xboole_0 @ X38 @ ( k10_relat_1 @ X39 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('33',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','39'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) ) @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k3_xboole_0 @ X38 @ ( k10_relat_1 @ X39 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('48',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k1_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('49',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','55'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ X0 ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['56','61','62'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y40fXI8C3W
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.04/5.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.04/5.22  % Solved by: fo/fo7.sh
% 5.04/5.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.04/5.22  % done 8176 iterations in 4.760s
% 5.04/5.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.04/5.22  % SZS output start Refutation
% 5.04/5.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.04/5.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.04/5.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.04/5.22  thf(sk_A_type, type, sk_A: $i).
% 5.04/5.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.04/5.22  thf(sk_B_type, type, sk_B: $i).
% 5.04/5.22  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 5.04/5.22  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.04/5.22  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.04/5.22  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 5.04/5.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.04/5.22  thf(t146_funct_1, conjecture,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ B ) =>
% 5.04/5.22       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.04/5.22         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 5.04/5.22  thf(zf_stmt_0, negated_conjecture,
% 5.04/5.22    (~( ![A:$i,B:$i]:
% 5.04/5.22        ( ( v1_relat_1 @ B ) =>
% 5.04/5.22          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 5.04/5.22            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 5.04/5.22    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 5.04/5.22  thf('0', plain,
% 5.04/5.22      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf(t148_relat_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ B ) =>
% 5.04/5.22       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 5.04/5.22  thf('1', plain,
% 5.04/5.22      (![X26 : $i, X27 : $i]:
% 5.04/5.22         (((k2_relat_1 @ (k7_relat_1 @ X26 @ X27)) = (k9_relat_1 @ X26 @ X27))
% 5.04/5.22          | ~ (v1_relat_1 @ X26))),
% 5.04/5.22      inference('cnf', [status(esa)], [t148_relat_1])).
% 5.04/5.22  thf(t169_relat_1, axiom,
% 5.04/5.22    (![A:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ A ) =>
% 5.04/5.22       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 5.04/5.22  thf('2', plain,
% 5.04/5.22      (![X30 : $i]:
% 5.04/5.22         (((k10_relat_1 @ X30 @ (k2_relat_1 @ X30)) = (k1_relat_1 @ X30))
% 5.04/5.22          | ~ (v1_relat_1 @ X30))),
% 5.04/5.22      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.04/5.22  thf('3', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 5.04/5.22            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 5.04/5.22          | ~ (v1_relat_1 @ X1)
% 5.04/5.22          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 5.04/5.22      inference('sup+', [status(thm)], ['1', '2'])).
% 5.04/5.22  thf(dt_k7_relat_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 5.04/5.22  thf('4', plain,
% 5.04/5.22      (![X24 : $i, X25 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k7_relat_1 @ X24 @ X25)))),
% 5.04/5.22      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.04/5.22  thf('5', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X1)
% 5.04/5.22          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 5.04/5.22              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 5.04/5.22      inference('clc', [status(thm)], ['3', '4'])).
% 5.04/5.22  thf('6', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf(t28_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.04/5.22  thf('7', plain,
% 5.04/5.22      (![X15 : $i, X16 : $i]:
% 5.04/5.22         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 5.04/5.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.04/5.22  thf('8', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 5.04/5.22      inference('sup-', [status(thm)], ['6', '7'])).
% 5.04/5.22  thf('9', plain,
% 5.04/5.22      (![X30 : $i]:
% 5.04/5.22         (((k10_relat_1 @ X30 @ (k2_relat_1 @ X30)) = (k1_relat_1 @ X30))
% 5.04/5.22          | ~ (v1_relat_1 @ X30))),
% 5.04/5.22      inference('cnf', [status(esa)], [t169_relat_1])).
% 5.04/5.22  thf(t167_relat_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ B ) =>
% 5.04/5.22       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 5.04/5.22  thf('10', plain,
% 5.04/5.22      (![X28 : $i, X29 : $i]:
% 5.04/5.22         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 5.04/5.22          | ~ (v1_relat_1 @ X28))),
% 5.04/5.22      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.04/5.22  thf('11', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf(t8_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i,C:$i]:
% 5.04/5.22     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 5.04/5.22       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 5.04/5.22  thf('12', plain,
% 5.04/5.22      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.04/5.22         (~ (r1_tarski @ X19 @ X20)
% 5.04/5.22          | ~ (r1_tarski @ X21 @ X20)
% 5.04/5.22          | (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ X20))),
% 5.04/5.22      inference('cnf', [status(esa)], [t8_xboole_1])).
% 5.04/5.22  thf('13', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 5.04/5.22          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)))),
% 5.04/5.22      inference('sup-', [status(thm)], ['11', '12'])).
% 5.04/5.22  thf('14', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ sk_B)
% 5.04/5.22          | (r1_tarski @ (k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)) @ 
% 5.04/5.22             (k1_relat_1 @ sk_B)))),
% 5.04/5.22      inference('sup-', [status(thm)], ['10', '13'])).
% 5.04/5.22  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('16', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (r1_tarski @ (k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)) @ 
% 5.04/5.22          (k1_relat_1 @ sk_B))),
% 5.04/5.22      inference('demod', [status(thm)], ['14', '15'])).
% 5.04/5.22  thf(d10_xboole_0, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.04/5.22  thf('17', plain,
% 5.04/5.22      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 5.04/5.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.04/5.22  thf('18', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 5.04/5.22      inference('simplify', [status(thm)], ['17'])).
% 5.04/5.22  thf(t10_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i,C:$i]:
% 5.04/5.22     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 5.04/5.22  thf('19', plain,
% 5.04/5.22      (![X5 : $i, X6 : $i, X7 : $i]:
% 5.04/5.22         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 5.04/5.22      inference('cnf', [status(esa)], [t10_xboole_1])).
% 5.04/5.22  thf('20', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.04/5.22      inference('sup-', [status(thm)], ['18', '19'])).
% 5.04/5.22  thf(t12_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.04/5.22  thf('21', plain,
% 5.04/5.22      (![X11 : $i, X12 : $i]:
% 5.04/5.22         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 5.04/5.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.04/5.22  thf('22', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 5.04/5.22           = (k2_xboole_0 @ X1 @ X0))),
% 5.04/5.22      inference('sup-', [status(thm)], ['20', '21'])).
% 5.04/5.22  thf(t11_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i,C:$i]:
% 5.04/5.22     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.04/5.22  thf('23', plain,
% 5.04/5.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.04/5.22         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 5.04/5.22      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.04/5.22  thf('24', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.22         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 5.04/5.22      inference('sup-', [status(thm)], ['22', '23'])).
% 5.04/5.22  thf('25', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (r1_tarski @ (k10_relat_1 @ sk_B @ X0) @ (k1_relat_1 @ sk_B))),
% 5.04/5.22      inference('sup-', [status(thm)], ['16', '24'])).
% 5.04/5.22  thf('26', plain,
% 5.04/5.22      (![X2 : $i, X4 : $i]:
% 5.04/5.22         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 5.04/5.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.04/5.22  thf('27', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 5.04/5.22          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 5.04/5.22      inference('sup-', [status(thm)], ['25', '26'])).
% 5.04/5.22  thf('28', plain,
% 5.04/5.22      ((~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 5.04/5.22        | ~ (v1_relat_1 @ sk_B)
% 5.04/5.22        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 5.04/5.22      inference('sup-', [status(thm)], ['9', '27'])).
% 5.04/5.22  thf('29', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 5.04/5.22      inference('simplify', [status(thm)], ['17'])).
% 5.04/5.22  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('31', plain,
% 5.04/5.22      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 5.04/5.22      inference('demod', [status(thm)], ['28', '29', '30'])).
% 5.04/5.22  thf(t139_funct_1, axiom,
% 5.04/5.22    (![A:$i,B:$i,C:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ C ) =>
% 5.04/5.22       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 5.04/5.22         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 5.04/5.22  thf('32', plain,
% 5.04/5.22      (![X38 : $i, X39 : $i, X40 : $i]:
% 5.04/5.22         (((k10_relat_1 @ (k7_relat_1 @ X39 @ X38) @ X40)
% 5.04/5.22            = (k3_xboole_0 @ X38 @ (k10_relat_1 @ X39 @ X40)))
% 5.04/5.22          | ~ (v1_relat_1 @ X39))),
% 5.04/5.22      inference('cnf', [status(esa)], [t139_funct_1])).
% 5.04/5.22  thf('33', plain,
% 5.04/5.22      (![X28 : $i, X29 : $i]:
% 5.04/5.22         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 5.04/5.22          | ~ (v1_relat_1 @ X28))),
% 5.04/5.22      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.04/5.22  thf('34', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.22         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.04/5.22           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 5.04/5.22          | ~ (v1_relat_1 @ X1)
% 5.04/5.22          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 5.04/5.22      inference('sup+', [status(thm)], ['32', '33'])).
% 5.04/5.22  thf('35', plain,
% 5.04/5.22      (![X24 : $i, X25 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k7_relat_1 @ X24 @ X25)))),
% 5.04/5.22      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.04/5.22  thf('36', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X1)
% 5.04/5.22          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 5.04/5.22             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 5.04/5.22      inference('clc', [status(thm)], ['34', '35'])).
% 5.04/5.22  thf('37', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         ((r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 5.04/5.22           (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))
% 5.04/5.22          | ~ (v1_relat_1 @ sk_B))),
% 5.04/5.22      inference('sup+', [status(thm)], ['31', '36'])).
% 5.04/5.22  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('39', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 5.04/5.22          (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))),
% 5.04/5.22      inference('demod', [status(thm)], ['37', '38'])).
% 5.04/5.22  thf('40', plain,
% 5.04/5.22      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 5.04/5.22      inference('sup+', [status(thm)], ['8', '39'])).
% 5.04/5.22  thf(t87_relat_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]:
% 5.04/5.22     ( ( v1_relat_1 @ B ) =>
% 5.04/5.22       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 5.04/5.22  thf('41', plain,
% 5.04/5.22      (![X36 : $i, X37 : $i]:
% 5.04/5.22         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X36 @ X37)) @ X37)
% 5.04/5.22          | ~ (v1_relat_1 @ X36))),
% 5.04/5.22      inference('cnf', [status(esa)], [t87_relat_1])).
% 5.04/5.22  thf('42', plain,
% 5.04/5.22      (![X2 : $i, X4 : $i]:
% 5.04/5.22         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 5.04/5.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.04/5.22  thf('43', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X1)
% 5.04/5.22          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 5.04/5.22          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 5.04/5.22      inference('sup-', [status(thm)], ['41', '42'])).
% 5.04/5.22  thf('44', plain,
% 5.04/5.22      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 5.04/5.22        | ~ (v1_relat_1 @ sk_B))),
% 5.04/5.22      inference('sup-', [status(thm)], ['40', '43'])).
% 5.04/5.22  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('46', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 5.04/5.22      inference('demod', [status(thm)], ['44', '45'])).
% 5.04/5.22  thf('47', plain,
% 5.04/5.22      (![X38 : $i, X39 : $i, X40 : $i]:
% 5.04/5.22         (((k10_relat_1 @ (k7_relat_1 @ X39 @ X38) @ X40)
% 5.04/5.22            = (k3_xboole_0 @ X38 @ (k10_relat_1 @ X39 @ X40)))
% 5.04/5.22          | ~ (v1_relat_1 @ X39))),
% 5.04/5.22      inference('cnf', [status(esa)], [t139_funct_1])).
% 5.04/5.22  thf('48', plain,
% 5.04/5.22      (![X28 : $i, X29 : $i]:
% 5.04/5.22         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ (k1_relat_1 @ X28))
% 5.04/5.22          | ~ (v1_relat_1 @ X28))),
% 5.04/5.22      inference('cnf', [status(esa)], [t167_relat_1])).
% 5.04/5.22  thf('49', plain,
% 5.04/5.22      (![X15 : $i, X16 : $i]:
% 5.04/5.22         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 5.04/5.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.04/5.22  thf('50', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X0)
% 5.04/5.22          | ((k3_xboole_0 @ (k10_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 5.04/5.22              = (k10_relat_1 @ X0 @ X1)))),
% 5.04/5.22      inference('sup-', [status(thm)], ['48', '49'])).
% 5.04/5.22  thf(commutativity_k3_xboole_0, axiom,
% 5.04/5.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.04/5.22  thf('51', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.04/5.22  thf('52', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X0)
% 5.04/5.22          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 5.04/5.22              = (k10_relat_1 @ X0 @ X1)))),
% 5.04/5.22      inference('demod', [status(thm)], ['50', '51'])).
% 5.04/5.22  thf('53', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.22         (((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 5.04/5.22            (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 5.04/5.22            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 5.04/5.22          | ~ (v1_relat_1 @ X1)
% 5.04/5.22          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 5.04/5.22      inference('sup+', [status(thm)], ['47', '52'])).
% 5.04/5.22  thf('54', plain,
% 5.04/5.22      (![X24 : $i, X25 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X24) | (v1_relat_1 @ (k7_relat_1 @ X24 @ X25)))),
% 5.04/5.22      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 5.04/5.22  thf('55', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.04/5.22         (~ (v1_relat_1 @ X1)
% 5.04/5.22          | ((k3_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 5.04/5.22              (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 5.04/5.22              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 5.04/5.22      inference('clc', [status(thm)], ['53', '54'])).
% 5.04/5.22  thf('56', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         (((k3_xboole_0 @ sk_A @ 
% 5.04/5.22            (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0)))
% 5.04/5.22            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 5.04/5.22          | ~ (v1_relat_1 @ sk_B))),
% 5.04/5.22      inference('sup+', [status(thm)], ['46', '55'])).
% 5.04/5.22  thf(t17_xboole_1, axiom,
% 5.04/5.22    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 5.04/5.22  thf('57', plain,
% 5.04/5.22      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.04/5.22      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.04/5.22  thf('58', plain,
% 5.04/5.22      (![X15 : $i, X16 : $i]:
% 5.04/5.22         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 5.04/5.22      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.04/5.22  thf('59', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 5.04/5.22           = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.22      inference('sup-', [status(thm)], ['57', '58'])).
% 5.04/5.22  thf('60', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.04/5.22  thf('61', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]:
% 5.04/5.22         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 5.04/5.22           = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.22      inference('demod', [status(thm)], ['59', '60'])).
% 5.04/5.22  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('63', plain,
% 5.04/5.22      (![X0 : $i]:
% 5.04/5.22         ((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ X0))
% 5.04/5.22           = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))),
% 5.04/5.22      inference('demod', [status(thm)], ['56', '61', '62'])).
% 5.04/5.22  thf('64', plain,
% 5.04/5.22      ((((k3_xboole_0 @ sk_A @ 
% 5.04/5.22          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 5.04/5.22          = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 5.04/5.22        | ~ (v1_relat_1 @ sk_B))),
% 5.04/5.22      inference('sup+', [status(thm)], ['5', '63'])).
% 5.04/5.22  thf('65', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 5.04/5.22      inference('demod', [status(thm)], ['44', '45'])).
% 5.04/5.22  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 5.04/5.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.04/5.22  thf('67', plain,
% 5.04/5.22      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 5.04/5.22         = (sk_A))),
% 5.04/5.22      inference('demod', [status(thm)], ['64', '65', '66'])).
% 5.04/5.22  thf('68', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.04/5.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.04/5.22  thf('69', plain,
% 5.04/5.22      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 5.04/5.22      inference('cnf', [status(esa)], [t17_xboole_1])).
% 5.04/5.22  thf('70', plain,
% 5.04/5.22      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 5.04/5.22      inference('sup+', [status(thm)], ['68', '69'])).
% 5.04/5.22  thf('71', plain,
% 5.04/5.22      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 5.04/5.22      inference('sup+', [status(thm)], ['67', '70'])).
% 5.04/5.22  thf('72', plain, ($false), inference('demod', [status(thm)], ['0', '71'])).
% 5.04/5.22  
% 5.04/5.22  % SZS output end Refutation
% 5.04/5.22  
% 5.04/5.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
