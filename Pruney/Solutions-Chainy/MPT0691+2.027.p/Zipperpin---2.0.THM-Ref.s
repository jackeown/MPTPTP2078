%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WrLV3Fgvru

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:21 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 243 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          :  765 (2119 expanded)
%              Number of equality atoms :   37 (  79 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X34 @ X33 ) @ X35 )
        = ( k3_xboole_0 @ X33 @ ( k10_relat_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X34 @ X33 ) @ X35 )
        = ( k3_xboole_0 @ X33 @ ( k10_relat_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) )
    = sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('24',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X34 @ X33 ) @ X35 )
        = ( k3_xboole_0 @ X33 @ ( k10_relat_1 @ X34 @ X35 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('33',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','37','39','40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WrLV3Fgvru
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 931 iterations in 0.375s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.83  thf(t146_funct_1, conjecture,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.83         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i,B:$i]:
% 0.60/0.83        ( ( v1_relat_1 @ B ) =>
% 0.60/0.83          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.60/0.83            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.60/0.83  thf('0', plain,
% 0.60/0.83      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(t139_funct_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ C ) =>
% 0.60/0.83       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.60/0.83         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.83         (((k10_relat_1 @ (k7_relat_1 @ X34 @ X33) @ X35)
% 0.60/0.83            = (k3_xboole_0 @ X33 @ (k10_relat_1 @ X34 @ X35)))
% 0.60/0.83          | ~ (v1_relat_1 @ X34))),
% 0.60/0.83      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.60/0.83  thf(dt_k7_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      (![X18 : $i, X19 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.83  thf(t169_relat_1, axiom,
% 0.60/0.83    (![A:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ A ) =>
% 0.60/0.83       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X27 : $i]:
% 0.60/0.83         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 0.60/0.83          | ~ (v1_relat_1 @ X27))),
% 0.60/0.83      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.60/0.83  thf(t170_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( r1_tarski @
% 0.60/0.83         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.60/0.83  thf('4', plain,
% 0.60/0.83      (![X28 : $i, X29 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ 
% 0.60/0.83           (k10_relat_1 @ X28 @ (k2_relat_1 @ X28)))
% 0.60/0.83          | ~ (v1_relat_1 @ X28))),
% 0.60/0.83      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.60/0.83  thf('5', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.60/0.83           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.60/0.83          | ~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (v1_relat_1 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['3', '4'])).
% 0.60/0.83  thf('6', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.60/0.83             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.60/0.83      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.83  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(t12_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X11 : $i, X12 : $i]:
% 0.60/0.83         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf(t11_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.83         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.60/0.83      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ sk_B)
% 0.60/0.83        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['6', '11'])).
% 0.60/0.83  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('14', plain,
% 0.60/0.83      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.60/0.83  thf(t28_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.83  thf('15', plain,
% 0.60/0.83      (![X16 : $i, X17 : $i]:
% 0.60/0.83         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.60/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.60/0.83         = (sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.83         (((k10_relat_1 @ (k7_relat_1 @ X34 @ X33) @ X35)
% 0.60/0.83            = (k3_xboole_0 @ X33 @ (k10_relat_1 @ X34 @ X35)))
% 0.60/0.83          | ~ (v1_relat_1 @ X34))),
% 0.60/0.83      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.60/0.83  thf(t167_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.60/0.83  thf('18', plain,
% 0.60/0.83      (![X25 : $i, X26 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 0.60/0.83          | ~ (v1_relat_1 @ X25))),
% 0.60/0.83      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.60/0.83  thf(d10_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X2 : $i, X4 : $i]:
% 0.60/0.83         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('20', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X0)
% 0.60/0.83          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.60/0.83          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)) @ 
% 0.60/0.83             (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X2))
% 0.60/0.83              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 0.60/0.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['17', '20'])).
% 0.60/0.83  thf('22', plain,
% 0.60/0.83      ((~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.60/0.83        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.60/0.83        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.60/0.83            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['16', '21'])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))
% 0.60/0.83         = (sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.83  thf('24', plain,
% 0.60/0.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.83         (((k10_relat_1 @ (k7_relat_1 @ X34 @ X33) @ X35)
% 0.60/0.83            = (k3_xboole_0 @ X33 @ (k10_relat_1 @ X34 @ X35)))
% 0.60/0.83          | ~ (v1_relat_1 @ X34))),
% 0.60/0.83      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.60/0.83  thf('25', plain,
% 0.60/0.83      (![X25 : $i, X26 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 0.60/0.83          | ~ (v1_relat_1 @ X25))),
% 0.60/0.83      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.60/0.83  thf('26', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         ((r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.60/0.83           (k1_relat_1 @ (k7_relat_1 @ X1 @ X2)))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['24', '25'])).
% 0.60/0.83  thf('27', plain,
% 0.60/0.83      (![X18 : $i, X19 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.83  thf('28', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1)
% 0.60/0.83          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.60/0.83             (k1_relat_1 @ (k7_relat_1 @ X1 @ X2))))),
% 0.60/0.83      inference('clc', [status(thm)], ['26', '27'])).
% 0.60/0.83  thf('29', plain,
% 0.60/0.83      (((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['23', '28'])).
% 0.60/0.83  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('31', plain,
% 0.60/0.83      ((r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.60/0.83  thf(t87_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.60/0.83  thf('32', plain,
% 0.60/0.83      (![X30 : $i, X31 : $i]:
% 0.60/0.83         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X30 @ X31)) @ X31)
% 0.60/0.83          | ~ (v1_relat_1 @ X30))),
% 0.60/0.83      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.60/0.83  thf('33', plain,
% 0.60/0.83      (![X2 : $i, X4 : $i]:
% 0.60/0.83         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('34', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.60/0.83          | ((X0) = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['32', '33'])).
% 0.60/0.83  thf('35', plain,
% 0.60/0.83      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['31', '34'])).
% 0.60/0.83  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('37', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.83  thf('38', plain,
% 0.60/0.83      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('39', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.60/0.83      inference('simplify', [status(thm)], ['38'])).
% 0.60/0.83  thf('40', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.83  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('42', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.60/0.83        | ((sk_A)
% 0.60/0.83            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.60/0.83      inference('demod', [status(thm)], ['22', '37', '39', '40', '41'])).
% 0.60/0.83  thf('43', plain,
% 0.60/0.83      ((~ (v1_relat_1 @ sk_B)
% 0.60/0.83        | ((sk_A)
% 0.60/0.83            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['2', '42'])).
% 0.60/0.83  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('45', plain,
% 0.60/0.83      (((sk_A)
% 0.60/0.83         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.60/0.83      inference('demod', [status(thm)], ['43', '44'])).
% 0.60/0.83  thf(t148_relat_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( v1_relat_1 @ B ) =>
% 0.60/0.83       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.60/0.83  thf('46', plain,
% 0.60/0.83      (![X20 : $i, X21 : $i]:
% 0.60/0.83         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.60/0.83          | ~ (v1_relat_1 @ X20))),
% 0.60/0.83      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.60/0.83  thf('47', plain,
% 0.60/0.83      (![X28 : $i, X29 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ X28 @ X29) @ 
% 0.60/0.83           (k10_relat_1 @ X28 @ (k2_relat_1 @ X28)))
% 0.60/0.83          | ~ (v1_relat_1 @ X28))),
% 0.60/0.83      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.60/0.83  thf('48', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.60/0.83           (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 0.60/0.83          | ~ (v1_relat_1 @ X1)
% 0.60/0.83          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['46', '47'])).
% 0.60/0.83  thf('49', plain,
% 0.60/0.83      (![X18 : $i, X19 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.83  thf('50', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X1)
% 0.60/0.83          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.60/0.83             (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 0.60/0.83      inference('clc', [status(thm)], ['48', '49'])).
% 0.60/0.83  thf('51', plain,
% 0.60/0.83      (((r1_tarski @ sk_A @ 
% 0.60/0.83         (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['45', '50'])).
% 0.60/0.83  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('53', plain,
% 0.60/0.83      ((r1_tarski @ sk_A @ 
% 0.60/0.83        (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['51', '52'])).
% 0.60/0.83  thf('54', plain,
% 0.60/0.83      (![X2 : $i, X4 : $i]:
% 0.60/0.83         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('55', plain,
% 0.60/0.83      ((~ (r1_tarski @ 
% 0.60/0.83           (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.60/0.83            (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.60/0.83           sk_A)
% 0.60/0.83        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.60/0.83            (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['53', '54'])).
% 0.60/0.83  thf('56', plain,
% 0.60/0.83      (![X18 : $i, X19 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.60/0.83      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.60/0.83  thf('57', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.83  thf('58', plain,
% 0.60/0.83      (![X25 : $i, X26 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 0.60/0.83          | ~ (v1_relat_1 @ X25))),
% 0.60/0.83      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.60/0.83  thf('59', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.60/0.83          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['57', '58'])).
% 0.60/0.83  thf('60', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (~ (v1_relat_1 @ sk_B)
% 0.60/0.83          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['56', '59'])).
% 0.60/0.83  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('62', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.60/0.83      inference('demod', [status(thm)], ['60', '61'])).
% 0.60/0.83  thf('63', plain,
% 0.60/0.83      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.60/0.83         = (sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['55', '62'])).
% 0.60/0.83  thf('64', plain,
% 0.60/0.83      ((((k3_xboole_0 @ sk_A @ 
% 0.60/0.83          (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.60/0.83        | ~ (v1_relat_1 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['1', '63'])).
% 0.60/0.83  thf('65', plain, ((v1_relat_1 @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('66', plain,
% 0.60/0.83      (((k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.60/0.83         = (sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['64', '65'])).
% 0.60/0.83  thf('67', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.60/0.83      inference('simplify', [status(thm)], ['38'])).
% 0.60/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.83  thf('68', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf(t18_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.60/0.83  thf('69', plain,
% 0.60/0.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.60/0.83         ((r1_tarski @ X13 @ X14)
% 0.60/0.83          | ~ (r1_tarski @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.60/0.83      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.60/0.83  thf('70', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['68', '69'])).
% 0.60/0.83  thf('71', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.60/0.83      inference('sup-', [status(thm)], ['67', '70'])).
% 0.60/0.83  thf('72', plain,
% 0.60/0.83      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['66', '71'])).
% 0.60/0.83  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
